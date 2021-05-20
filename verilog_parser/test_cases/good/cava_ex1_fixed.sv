// Copied from https://github.com/project-oak/silveroak/blob/5a6c7d9b378073be91fac7b973c688283daf4849/examples/README.md (called nand2 there)

module cava_ex1_fixed(
  input logic b,
  input logic a,
  output logic c,
// LIMITATION: Currently require clk input (easy to fix...)
  input logic clk);

// REMOVED:
// timeunit 1ns; timeprecision 1ns;

  logic net_0;
  logic net_1;
  logic net_2;
  logic net_3;
  logic net_4;
  logic net_5;

  // Constant nets
  assign net_0 = 1'b0;
  assign net_1 = 1'b1;
  // Wire up inputs.
  assign net_3 = b;
  assign net_2 = a;
  // Wire up outputs.
  assign c = net_5;

  not inst5 (net_5, net_4);
  and inst4 (net_4, net_2, net_3);

endmodule
