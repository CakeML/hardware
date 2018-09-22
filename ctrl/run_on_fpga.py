#!/usr/bin/env python3.6
#                    ^-- Pynq package seems to only be available for python 3.6

import argparse
from datetime import datetime
import os
import signal
import sys

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


# Super inefficient, should use string buffer instead
def print_interrupt_msg(mem):
    num = min(mem[0] & 0xFF, 63)

    for addr in range(0, 16):
        val = mem[addr]

        for i in range(4):
            # First byte is the length...
            if addr == 0 and i == 0:
                continue

            # Max number of chars reached?
            bytenum = 4*addr + i

            if bytenum > num:
                print()
                return

            # If not, print current char
            c = 0xFF & (val >> 8*i)
            print(chr(c), end='')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--debug", action="store_true")

    parser.add_argument("bit_file", metavar="bit-file",
                        help="FPGA bitstream to load onto the FPGA")
    parser.add_argument("--low_mem_padding", type=int, default=0)

    parser.add_argument('mems', nargs='+')
    args = parser.parse_args()

    # Sanity check params
    if len(args.mems) > 2:
        log("Too many mem params!")
        sys.exit(1)

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

        # 4-alignment required by CakeML, redundant, but just to be clear
        if mem_start % 4 != 0:
            log("Memory start not 4-aligned, exiting")
            sys.exit(1)

        # 64-alignment required by processor caches
        if mem_start % 64 != 0:
            log("Memory start not 64-aligned, exiting")
            sys.exit(1)

        # Load program from file
        log("Loading low mem at physical addr mem_start")
        low_mem_size = 0
        with open(args.mems[0]) as f:
            for i, val in enumerate(f):
                mem[args.low_mem_padding + i] = int(val, 16)
                #print("--> Wrote ", to_hex(int(val, 16)), "to addr", args.low_mem_padding + i)
                low_mem_size = i

        if len(args.mems) == 2:
            # TODO: This value should not be hard-coded,
            # and should be read from some memory input format instead
            heap_block = 31457239
            high_mem_start = (low_mem_size + 1) + heap_block
            log("Loading high mem at physical addr",
                format(high_mem_start + mem_start, '0x'))

            with open(args.mems[1]) as f:
                for i, val in enumerate(f):
                    mem[high_mem_start + i] = int(val, 16)

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

            print_interrupt_msg(mem)

            # Respond to interrupt
            core_ctrl.write(_CORE_CTRL_REG_INTERRUPT_ACK, 0)
            idev.write(bytes([0, 0, 0, 1]))


if __name__ == "__main__":
    main()
