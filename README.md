Verilog development and verification project for HOL4

# Important directories

The formal Verilog semantics is located in the directory `verilog`.

The verified Verilog synthesis tool Lutsig is located in the `compiler` directory. The proof-producing Verilog code generator is located in `translator`.

Some examples on how to use Lutsig and the code generator in practice are available in the `examples` directory. There is also a test-suite for Lutsig available, based on unverified parsing of Verilog text files, in the `verilog_parser` directory.

Silver-related theories and tools are located in the `ag32` directory.

# Installation and setup

The development requires [HOL4](https://hol-theorem-prover.org).

For Silver (ag32), additional setup is required, as described below.

## Silver setup

To build Silver-related theories, you need to point `$CAKEMLDIR` to your CakeML compiler directory.

Because the Verilog semantics has been updated since Silver was developed, the Silver theories will not build using the latest commit. If you want to build Silver, use e.g. dc281059bd3a19e478fb211aadda1c2ac7891fa9. (This is just a temporary workaround.)

### ISA generation

Translating the Silver ISA from L3 to HOL is not necessary as the already-translated ISA stored in the CakeML compiler project is used in all Silver theories.

However, after updating the L3 ISA the following steps are required to update the HOL ISA.

First, make sure you have [L3](http://www.cl.cam.ac.uk/~acjf3/l3) installed.

With L3 installed, the following command in the L3 REPL (named `l3`, located in the `bin` directory in your L3 directory) will produce the HOL ISA from the L3 ISA:

```
HolExport.spec ("ag32.spec", "ag32");
```
