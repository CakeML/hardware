#!/usr/bin/env python3

def to_hex(val):
    return '{0:0{1}x}'.format(val, 8)

prev = None

print("memory_initialization_radix=16;")
print("memory_initialization_vector=", end='')

with open("prg.data") as f:
    for i in range(8):
        print(0, '', end='')
    
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

print(';')    
