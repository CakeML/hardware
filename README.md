This is a snapshot of our Verilog verification and extraction development, produced for our paper "Proof-producing extraction to Verilog in HOL" submitted to FMCAD'18.

## Installation and setup

The development requires [HOL4](https://hol-theorem-prover.org). Make sure to build HOL4 from its Github repo rather than using the latest release. Try `master` first, and it that does not work try commit `6a81a0396baec5a4cea25172a67cc26eec59ffa9`.

Furthermore, you also need [L3](http://www.cl.cam.ac.uk/~acjf3/l3). L3 is not essential for using the extraction algorithm, but is used here because it will be relevant in future developments. After L3 has been installed, the following commands in the L3 REPL (named `l3`, located in the `bin` directory in your L3 directory) will produce HOL code describing the processor case study from the paper:

```
HolExport.spec ("tiny.spec", "tiny");
HolExport.spec ("tinyImpl.spec", "tinyImpl");
```

The file `tinyImpl.spec` describes the processor used in the case study, and `tiny.spec` is a high-level specification that is not relevant for this paper but is used in `tinyTestProgramsScript.sml` to encode assembly programs.

The development is set up to build the processor case study by default. After the above L3 setup, the development can be compiled by a simple `Holmake` call.

It is important to note that what you see in this repo is just a development snapshot, so some future things not included in the paper are included in the files here, and some of the new development contains cheats. Specifically, the cheat in `tinyTranslateLib.sml` is for future processor verification (how to handle writing outside the memory), the cheats in `translatorLib.sml` are for handling slice writes to arrays (which are needed for modeling more complex memories with byte-write support), and the cheats in `translatorScript.sml` concern translating shift operations.

## Relation between the paper and the formal development

The main purpose of this README is to bridge the gap between the paper and the formal development. Here follows, section-per-section, how what is said in the paper relates to the formal development.

### II. Example

The HOL next-state functions from the introductory example (`P`, `Q`, and `PQ`) are located in `circuitExampleScript.sml`. The theorem that is lifted to Verilog, called `PQ_ok` in the development, is located in the same file. The file `circuitExampleTranslatorScript.sml.disabled` shows how to lift `PQ_ok` to Verilog; the theorem shown in the paper is called `PQ_ok_verilog`. The file is "disabled" because the development is set up to build the processor case study by default. In the paper, in subsection "V.B. Pass two: full program extraction", we mention that some ugly but routine setup code is needed to use the extraction algorithm, and much of the code seen in `circuitExampleTranslatorScript.sml.disabled` is such ugly setup code. A more polished development would automate away more of this, as we mention in the paper.

### IV. Verilog

The file `verilogScript.sml` specifies the syntax and semantics of Verilog. For example, `exp` is the data type for expressions and `vprog` the data type for statements/processes. The names in the development differ somewhat from the paper, specifically the semantics of expressions are given by `erun` (called `step_{exp}` in the paper), of statements by `prun` (called `step` in the paper), and of collections of processes ("modules") by `mstep` (called `run` in the paper). In the paper it is mentioned that that `run`, the semantic function shown in the paper, and the actual semantics function used in the development (i.e., `mrun`) are "provably equal" -- this equivalence is proved in `verilogPaperScript.sml`, which is also where the semantics functions shown in the paper are defined.

### V. The extraction algorithm

The extraction algorithm is referred to as a "translator" in the development, and can be find in files with "translator" in their name. For the first phase, `translatorLib.sml` is the most interesting file, because there one will find the important function `hol2hardware_body`, which is the main entry-point to the extraction algorithm's first phase. For the second phase, `moduleTranslatorScript.sml` is the most interesting file. There we have the theorem `mstep_untainted_state`, which is used in e.g. `circuitExampleTranslatorScript.sml.disabled` to glue independent Verilog processes together into a module (in the theorem `PQ_ok_relM`). (The example `R` function shown in the paper is located in `circuitExampleScript.sml`.)

### VI. Processor case study

The file `tinyMachineScript.sml` defines the next-state function for the whole processor case study. But the main file of interest for the case study is `tinyTranslateLib.sml`, which extracts the case study processor to Verilog. In the end of the file there is a call to the pretty-print machinery which produces a `processor.sv` file, which can be used for Verilog simulation and synthesis.

The file `tinyTestProgramsScript.sml` includes two small example programs that we have tested on our FPGA board. As stated in the paper, it is unlikely that the processor is fully correct in its current shape: we expect to find various edge-case bugs when proving a correspondence between `tinyImpl.spec` and `tiny.spec` in future work.
