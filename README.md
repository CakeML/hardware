A HOL4 project for hardware/Verilog development

# Installation and setup

The development requires [HOL4](https://hol-theorem-prover.org) and [L3](http://www.cl.cam.ac.uk/~acjf3/l3). 

To build you need to point $CAKEMLDIR to your CakeML compiler directory.

## ISA generation

The following command in the L3 REPL (named `l3`, located in the `bin` directory in your L3 directory) will produce ISA HOL code from the ISA specification:

```
HolExport.spec ("ag32.spec", "ag32");
```

Doing this is not necessary as the generated ISA stored in the CakeML compiler project is used.
