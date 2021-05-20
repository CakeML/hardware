// Copied from https://github.com/project-oak/silveroak/blob/5a6c7d9b378073be91fac7b973c688283daf4849/examples/README.md (called fulladder there)

module cava_ex2(
  input logic cin,
  input logic b,
  input logic a,
  output logic carry,
  output logic sum
  );

// REMOVED:
// timeunit 1ns; timeprecision 1ns;

  logic[9:0] net;

  // Constant nets
  assign net[0] = 1'b0;
  assign net[1] = 1'b1;
  // Wire up inputs.
  assign net[4] = cin;
  assign net[3] = b;
  assign net[2] = a;
  // Wire up outputs.
  assign carry = net[9] ;
  assign sum = net[7] ;

  or inst9 (net[9],net[6],net[8]);
  and inst8 (net[8],net[5],net[4]);
  xor inst7 (net[7],net[5],net[4]);
  and inst6 (net[6],net[2],net[3]);
  xor inst5 (net[5],net[2],net[3]);

endmodule
