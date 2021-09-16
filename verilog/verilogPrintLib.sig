signature verilogPrintLib =
sig
 include Abbrev

 val verilog_print : string -> term -> string
end
