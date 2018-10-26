#!/usr/bin/env python3.6
#                    ^-- Pynq package seems to only be available for python 3.6

import argparse
from datetime import datetime
import os
import signal
import sys
import json

# Workaround for pynq overriding the default SIGINT handler for some reason
# (Hopefully no cleanup is done in custom handler?)
sigint_handler = signal.getsignal(signal.SIGINT)

from pynq import MMIO
from pynq import Overlay
from pynq import Xlnk

signal.signal(signal.SIGINT, sigint_handler)

import numpy as np

_CORE_CTRL_BASE_ADDRESS = 0x4000_0000
_CORE_CTRL_REG_MEM_START = 0
_CORE_CTRL_REG_INTERRUPT_ACK = 4

_date_format = "%Y-%m-%d %H:%M:%S"


def log(*msgs):
    print(datetime.now().strftime(_date_format), ": ", sep="", end="")
    print(*msgs)


def to_hex(val):
    return '{0:0{1}x}'.format(val, 8)


# Copied from some pynq example
def _get_uio_device(irq):
    dev_names = None
    with open('/proc/interrupts', 'r') as f:
        for line in f:
            cols = line.split()
            if len(cols) >= 7:
                if cols[4] == str(irq):
                    # Hack to work on multiple kernel versions
                    dev_names = [cols[5], cols[6]]

    if dev_names is None:
        return None

    for dev in os.listdir("/sys/class/uio"):
        with open('/sys/class/uio/' + dev + '/name', 'r') as f:
            name = f.read().strip()
        if name in dev_names:
            return '/dev/' + dev

    return None


def tokenize(s):
    return filter(lambda s: s, s.split(' '))


def word_of_bytes(bs):
    return bs[0] | (bs[1] << 8) | (bs[2] << 2*8) | (bs[3] << 3*8)


def words_of_bytes(bs):
    lenbs = len(bs)

    if lenbs >= 4:
        return [word_of_bytes(bs[:4])] + words_of_bytes(bs[4:])
    elif lenbs == 3:
        return [bs[0] | (bs[1] << 8) | (bs[2] << 2*8)]
    elif lenbs == 2:
        return [bs[0] | (bs[1] << 8)]
    elif lenbs == 1:
        return [bs[0]]
    else:
        return []


def flatten(l):
    return sum(l, [])


def print_debug_char(c):
    print(c, chr(c))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--debug", action="store_true")
    parser.add_argument("--args", help="Argv arguments, note that separate arguments must be separates by spaces only")
    parser.add_argument("--stdin", help="Contents to preload stdin buffer with")

    parser.add_argument("bit_file", metavar="bit-file",
                        help="FPGA bitstream to load onto the FPGA")

    parser.add_argument('program')
    args = parser.parse_args()

    with open(args.program) as f:
        jsonprg = json.load(f)

    # Interrupt handling
    idev_file = _get_uio_device(61)
    log("Interrupt device:", idev_file)
    idev = open(idev_file, 'r+b', buffering=0)

    # Clear potential previous interrupts
    idev.write(bytes([0, 0, 0, 1]))

    # Allocate memory for verified core; 128 MB is maximum allowed by kernel.
    # By default no caching is allowed, which is what we want here
    with Xlnk().cma_array(shape=(int((1.28*10**8)/4),), dtype=np.uint32) as mem:
        mem_start = mem.physical_address
        log("Memory starts at", format(mem_start, '0x'))

        # 4-alignment required by CakeML
        if mem_start % 4 != 0:
            log("Memory start not 4-aligned, exiting")
            sys.exit(1)

        # 64-alignment required by processor caches (currently disabled),
        # redundant, but just to be clear
        if mem_start % 64 != 0:
            log("Memory start not 64-aligned, exiting")
            sys.exit(1)

        # Load startup code
        log("Loading startup code at physical addr mem_start")
        for i, val in enumerate(jsonprg["startup_code"]):
            mem[i] = val
            #print("--> Wrote ", to_hex(int(val, 16)), "to addr", args.low_mem_padding + i)

        # Pointer to where to write next in memory...
        mempointer = len(jsonprg["startup_code"])

        # Write cline
        log("Cline...")

        cline_args_size = jsonprg["cline_args_size"]

        if args.args is None:
            mempointer += 1 + cline_args_size
        else:
            cakeml_args = tokenize(args.args)

            # cline arg count
            mem[mempointer] = len(cakeml_args)
            mempointer += 1

            # cline args
            cakeml_args = flatten(map(lambda arg: map(ord, arg) + [0], cakeml_args))

            if len(cakeml_args) >= 4*cline_args_size:
                log("Too long program arguments")
                sys.exit(1)

            if not all(map(allowed_char, cakeml_args)):
                log('Program arguments contain illegal chars')
                sys.exit(1)

            for i, w in enumerate(words_of_bytes(cakeml_args)):
                mem[mempointer + i] = w

            mempointer += cline_args_size

        # stdin

        # stdin pointer
        mempointer += 1

        if args.stdin is None:
            stdin = bytes()
        else:
            with open(args.stdin, 'rb') as f:
                stdin = f.read()

        # stdin length
        mem[mempointer] = len(stdin)
        mempointer += 1

        # stdin
        for i, w in enumerate(words_of_bytes(stdin)):
            mem[mempointer + i] = w

        mempointer += jsonprg["stdin_size"]

        start_of_stdin = mempointer

        # stderr + stdout not written from python script...

        mempointer += jsonprg["output_buffer_size"]

        # ffi code

        for i, w in enumerate(jsonprg["ffi_code"]):
            mem[mempointer + i] = w

        mempointer += len(jsonprg["ffi_code"])

        # skip stack/heap as well

        mempointer += jsonprg["heap_and_stack_size"]

        # ffi call jumps + cakeml data + code
        for i, w in enumerate(jsonprg["top_mem"]):
            mem[mempointer + i] = w

        # Setup FPGA
        ol = Overlay(args.bit_file)
        core_ctrl = MMIO(_CORE_CTRL_BASE_ADDRESS, 16)

        # Useful if we want to sync with a hardware debugger
        if args.debug:
            input("Press anything to start:")

        core_ctrl.write(_CORE_CTRL_REG_MEM_START, mem_start)

        log("Setup done, waiting for interrupts...")

        while True:
            interrupt_num = idev.read(4)

            log("Got interrupt", interrupt_num, "!")

            #print_interrupt_msg(mem, start_of_stdin)
            for i in range(0, 10):
                w = mem[start_of_stdin + i]

                print_debug_char(w & 0xFF)
                print_debug_char((w >> 8*1) & 0xFF)
                print_debug_char((w >> 8*2) & 0xFF)
                print_debug_char((w >> 8*3) & 0xFF)

            # Respond to interrupt
            core_ctrl.write(_CORE_CTRL_REG_INTERRUPT_ACK, 0)
            idev.write(bytes([0, 0, 0, 1]))


if __name__ == "__main__":
    main()
