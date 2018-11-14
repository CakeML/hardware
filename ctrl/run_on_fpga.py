#!/usr/bin/env python3.6
#                    ^-- Pynq package seems to only be available for python 3.6

import argparse
from datetime import datetime
import os
import signal
import sys
import json
import math
from itertools import zip_longest
import gc

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
_prg_name = "noname"

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
    return list(filter(lambda s: s, s.split(' ')))


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


# https://stackoverflow.com/questions/434287
def grouper(iterable, n, fillvalue=None):
    args = [iter(iterable)] * n
    return zip_longest(*args, fillvalue=fillvalue)


def words_of_bytes_cheap(bs):
    return map(word_of_bytes, grouper(bs, 4, 0))


def flatten(l):
    return sum(l, [])


def print_debug_char(c):
    print(c, chr(c))


def convert_ffi_word32(w):
    return ((w << 8*3) & 0xFF000000) | ((w << 8) & 0xFF0000) | ((w >> 8) & 0xFF00) | ((w >> 8*3) & 0xFF)


# Super inefficient, should use string buffer instead
def print_ffi_write_data(mem, base, num):
    for addr in range(0, num + (4 - num) % 4):
        val = mem[base + addr]

        for i in range(4):
            # Max number of chars reached?
            bytenum = 4*addr + i

            if bytenum >= num:
                print()
                return

            # If not, print current char
            c = 0xFF & (val >> 8*i)
            print(chr(c), end='')

    print()


ffi_id_to_name = {
    0: "empty",
    1: "get_arg_count",
    2: "get_arg_length",
    3: "get_arg",
    4: "read",
    5: "write",
    6: "open_in",
    7: "open_out",
    8: "close",
    9: "exit"}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--debug", action="store_true")
    parser.add_argument("--args", help="Argv arguments, note that separate arguments must be separates by spaces only")
    parser.add_argument("--stdin", help="Contents to preload stdin buffer with")
    parser.add_argument("--largeprogram", action="store_true")

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
        cline_args_size = jsonprg["cline_args_size"]

        if args.args is None:
            cakeml_args = [_prg_name]
        else:
            cakeml_args = [_prg_name] + tokenize(args.args)

        # cline arg count
        mem[mempointer] = len(cakeml_args)
        mempointer += 1

        log("Got {} cl argument(s) (including program name)".format(len(cakeml_args)))

        # cline args
        cakeml_args = flatten(map(lambda arg: list(map(ord, arg)) + [0], cakeml_args))

        if len(cakeml_args) >= 4*cline_args_size:
            log("Too long program arguments")
            sys.exit(1)

        if False: #not all(map(allowed_char, cakeml_args)):
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

        stdin_words = list(words_of_bytes_cheap(stdin))

        if len(stdin_words) >= jsonprg["stdin_size"]:
            log('Stdin too long')
            sys.exit(1)

        # stdin
        for i, w in enumerate(stdin_words):
            mem[mempointer + i] = w

        mempointer += jsonprg["stdin_size"]

        # stderr + stdout not written from python script...

        start_of_stdout = mempointer

        mempointer += jsonprg["output_buffer_size"]

        start_ffi_call_id = mempointer - 1

        # ffi code

        for i, w in enumerate(jsonprg["ffi_code"]):
            mem[mempointer + i] = w

        mempointer += len(jsonprg["ffi_code"])

        # skip stack/heap as well

        mempointer += jsonprg["heap_and_stack_size"]

        # ffi call jumps + cakeml data + code
        if args.largeprogram:
            for i, w in enumerate(jsonprg["ffi_jumps"]):
                mem[mempointer + i] = w
            mempointer += len(jsonprg["ffi_jumps"])

            cakeml_code_words = list(words_of_bytes_cheap(jsonprg["cakeml_code_bytes"]))
            for i, w in enumerate(cakeml_code_words):
                mem[mempointer + i] = w
            mempointer += len(cakeml_code_words)

            for i, w in enumerate(jsonprg["cakeml_data"]):
                mem[mempointer + i] = w
            #mempointer += len(jsonprg["ffi_jumps"])
        else:
            for i, w in enumerate(jsonprg["top_mem"]):
                mem[mempointer + i] = w

        # Don't need the json file anymore!
        # (Not sure how much this actually helps,
        # there are a lot of other things floating around as well.)
        del jsonprg
        gc.collect()

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

            w = mem[start_ffi_call_id]
            ffi_call_id = convert_ffi_word32(w)
            print("ffi call id:", ffi_id_to_name[ffi_call_id])

            if ffi_call_id == 5:
                read_len = convert_ffi_word32(mem[start_of_stdout + 2])
                print("length:", read_len)

                print("data:", end='')
                print_ffi_write_data(mem, start_of_stdout + 3, read_len)

                #for i in range(0, 10):
                #    w = mem[start_of_stdout + 3 + i]

                #    print_debug_char(w & 0xFF)
                #    print_debug_char((w >> 8*1) & 0xFF)
                #    print_debug_char((w >> 8*2) & 0xFF)
                #    print_debug_char((w >> 8*3) & 0xFF)

            # Respond to interrupt
            core_ctrl.write(_CORE_CTRL_REG_INTERRUPT_ACK, 0)
            idev.write(bytes([0, 0, 0, 1]))


if __name__ == "__main__":
    main()
