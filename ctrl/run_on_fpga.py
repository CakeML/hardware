#!/usr/bin/env python3.6

#                    ^-- Pynq package seems to only be available for python 3.6

import argparse
from datetime import datetime
import os
import signal

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


def print_interrupt_msg(mem):
    for addr in range(16):
        val = mem[addr]

        for i in range(4):
            c = 0xFF & (val >> 8*i)

            if c == 0:
                print()
                return
            else:
                print(chr(c), end='')


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("bit_file", metavar="bit-file")
    args = parser.parse_args()

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
        # TODO: Check if mem_start is aligned?

        # Load program:
        mem[16 + 0] = 0x800002
        mem[16 + 1] = 0x83000048
        mem[16 + 2] = 0x20003
        mem[16 + 3] = 0x820000
        mem[16 + 4] = 0x83000045
        mem[16 + 5] = 0x20003
        mem[16 + 6] = 0x820000
        mem[16 + 7] = 0x8300004C
        mem[16 + 8] = 0x20003
        mem[16 + 9] = 0x820000
        mem[16 + 10] = 0x20003
        mem[16 + 11] = 0x820000
        mem[16 + 12] = 0x8300004F
        mem[16 + 13] = 0x20003
        mem[16 + 14] = 0x820000
        mem[16 + 15] = 0x800003
        mem[16 + 16] = 0x8081000C
        mem[16 + 17] = 0x0
        mem[16 + 18] = 0x890089

        # Setup FPGA
        ol = Overlay(args.bit_file)
        core_ctrl = MMIO(_CORE_CTRL_BASE_ADDRESS, 16)

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
