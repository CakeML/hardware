Verilog development and verification project for HOL4

# Installation and setup

The development requires [HOL4](https://hol-theorem-prover.org).

## Ag32-specific setup

To build Ag32-related theories, such as the processor itself and `cakeml_connection`, you need to point `$CAKEMLDIR` to your CakeML compiler directory.

### ISA generation

Translating the Silver ISA from L3 to HOL is not necessary as the already-translated ISA stored in the CakeML compiler project is used.

However, after updating the L3 ISA the following steps are required to update the HOL ISA.

First, make sure you have [L3](http://www.cl.cam.ac.uk/~acjf3/l3) installed.

With L3 installed, the following command in the L3 REPL (named `l3`, located in the `bin` directory in your L3 directory) will produce the HOL ISA from the L3 ISA:

```
HolExport.spec ("ag32.spec", "ag32");
```
