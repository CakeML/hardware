#!/usr/bin/env python3

i = 0

with open("prg.data") as f:
    for l in f:
        print("mem[16 + ", i, "] = 0x", l, sep='', end='')
        i = i + 1
