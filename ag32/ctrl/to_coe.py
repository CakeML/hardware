#!/usr/bin/env python3

import argparse

def to_hex(val):
    return '{0:0{1}x}'.format(val, 8)

print("memory_initialization_radix=16;")
print("memory_initialization_vector=", end='')

parser = argparse.ArgumentParser()
parser.add_argument("memfile")
args = parser.parse_args()

prev = None

with open(args.memfile) as f:
    for l in f:
        if prev is None:
            prev = to_hex(int(l, 16))
        else:
            print(to_hex(int(l, 16)), end='')
            print(prev, '', end='')
            prev = None

if not prev is None:
    print(to_hex(0), end='')
    print(prev, end='')

#with open(args.memfile) as f:
#    for l in f:
#        print(to_hex(int(l, 16)), end=' ')

print(';')
