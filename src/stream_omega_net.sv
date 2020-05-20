// Copyright (c) 2020 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Wolfgang Roenninger <wroennin@ethz.ch>

/// Omega network using multiple `stream_xbar` as switches.
///
/// An omega network is isomorphic to a butterfly network.
///
/// Handshaking rules as defined by the `AMBA AXI` standard on default.
module stream_omega_net #(
  /// Number of inputs into the network (`> 0`).
  parameter int unsigned NumInp      = 32'd0,
  /// Number of outputs from the network (`> 0`).
  parameter int unsigned NumOut      = 32'd0,
  /// Radix of the individual switch points of the network.
  /// Currently supported are `32'd2` and `32'd4`.
  parameter int unsigned Radix       = 32'd2,
  /// Data width of the stream. Can be overwritten by defining the type parameter `payload_t`.
  parameter int unsigned DataWidth   = 32'd1,
  /// Payload type of the data ports, only usage of parameter `DataWidth`.
  parameter type         payload_t   = logic [DataWidth-1:0],
  /// Adds a spill register stage at each output.
  parameter bit          SpillReg = 1'b0,
  /// Use external priority for the individual `rr_arb_trees`.
  parameter int unsigned ExtPrio     = 1'b0,
  /// Use strict AXI valid ready handshaking.
  /// To be protocol conform also the parameter `LockIn` has to be set.
  parameter int unsigned AxiVldRdy   = 1'b1,
  /// Lock in the arbitration decision of the `rr_arb_tree`.
  /// When this is set, valids have to be asserted until the corresponding transaction is indicated
  /// by ready.
  parameter int unsigned LockIn      = 1'b1,
  /// Derived parameter, do **not** overwrite!
  ///
  /// Width of the output selection signal.
  parameter int unsigned SelWidth = (NumOut > 32'd1) ? unsigned'($clog2(NumOut)) : 32'd1,
  /// Derived parameter, do **not** overwrite!
  ///
  /// Signal type definition for selecting the output at the inputs.
  parameter type sel_oup_t = logic[SelWidth-1:0],
  /// Derived parameter, do **not** overwrite!
  ///
  /// Width of the input index signal.
  parameter int unsigned IdxWidth = (NumInp > 32'd1) ? unsigned'($clog2(NumInp)) : 32'd1,
  /// Derived parameter, do **not** overwrite!
  ///
  /// Signal type definition indicating from which input the output came.
  parameter type idx_inp_t = logic[IdxWidth-1:0]
) (
  /// Clock, positive edge triggered.
  input  logic                  clk_i,
  /// Asynchronous reset, active low.
  input  logic                  rst_ni,
  /// Flush the state of the internal `rr_arb_tree` modules.
  /// If not used set to `0`.
  /// Flush should only be used if there are no active `valid_i`, otherwise it will
  /// not adhere to the AXI handshaking.
  input  logic                  flush_i,
  /// Provide an external state for the `rr_arb_tree` models.
  /// Will only do something if ExtPrio is `1` otherwise tie to `0`.
  input  idx_inp_t [NumOut-1:0] rr_i,
  /// Input data ports.
  /// Has to be stable as long as `valid_i` is asserted when parameter `AxiVldRdy` is set.
  input  payload_t [NumInp-1:0] data_i,
  /// Selection of the output port where the data should be routed.
  /// Has to be stable as long as `valid_i` is asserted and parameter `AxiVldRdy` is set.
  input  sel_oup_t [NumInp-1:0] sel_i,
  /// Input is valid.
  input  logic     [NumInp-1:0] valid_i,
  /// Input is ready to accept data.
  output logic     [NumInp-1:0] ready_o,
  /// Output data ports. Valid if `valid_o = 1`
  output payload_t [NumOut-1:0] data_o,
  /// Index of the input port where data came from.
  output idx_inp_t [NumOut-1:0] idx_o,
  /// Output is valid.
  output logic     [NumOut-1:0] valid_o,
  /// Output can be accepted.
  input  logic     [NumOut-1:0] ready_i
);


  // Find the next power of two of either the number of inputs or number of outputs.
  // This normalizes the network to a power of two. Unused inputs and outputs are tied off.
  localparam int unsigned NumLanes = (NumOut > NumInp) ?
      unsigned'(2**$clog2(NumOut)) : unsigned'(2**$clog2(NumInp));

  // Find the number of routing levels needed.
  localparam int unsigned NumLevels = unsigned'(($clog2(NumOut)+$clog2(Radix)-1)/$clog2(Radix));

  // Find the number of routes per network stage.
  localparam int unsigned NumRouters = NumLanes / Radix;

  // Define the type of sel signal for the individual stages. This can be different than `sel_oup_t`
  // on `Radix` an additional time, as in higher radicies
  typedef logic [$clog2(NumLanes)-1:0] sel_t;

  // Define the payload which should be routed through the network.
  typedef struct packed {
    sel_t     sel_oup; // Selection of output, where it should be routed
    payload_t payload; // External payload data
    idx_inp_t idx_inp; // Index of the input of this packet
  } omega_data_t;

  initial begin : proc_debug_print
    $display("NumInp:     %0d", NumInp);
    $display("NumOut:     %0d", NumOut);
    $display("Radix:      %0d", Radix);
    $display("NumLanes:   %0d", NumLanes);
    $display("NumLevels:  %0d", NumLevels);
    $display("NumRouters: %0d", NumRouters);
  end






  // signal definitions
  omega_data_t [NumLevels-1:0][NumRouters-1:0][Radix-1:0] inp_router_data;
  logic        [NumLevels-1:0][NumRouters-1:0][Radix-1:0] inp_router_valid, inp_router_ready;
  omega_data_t [NumLevels-1:0][NumRouters-1:0][Radix-1:0] out_router_data;
  logic        [NumLevels-1:0][NumRouters-1:0][Radix-1:0] out_router_valid, out_router_ready;




  // Generate the `stream_xbar_routers`
  for (genvar i_level = 0; i_level < NumLevels; i_level++) begin : gen_
    /* code */
  end




  initial begin
    automatic int unsigned levels;
    automatic int unsigned rad = 32'd2;
    for (int unsigned i = 0; i < 32'd128; i++) begin
      levels = unsigned'(($clog2(i)+$clog2(rad)-1)/$clog2(rad));
      $display("Radix: %d: Num: %d NumLevels: %0d", rad, i, levels);
    end
    rad = 32'd4;
    for (int unsigned i = 0; i < 32'd128; i++) begin
      levels = unsigned'(($clog2(i)+$clog2(rad)-1)/$clog2(rad));
      $display("Radix: %d: Num: %d NumLevels: %0d", rad, i, levels);
    end
    rad = 32'd8;
    for (int unsigned i = 0; i < 32'd128; i++) begin
      levels = unsigned'(($clog2(i)+$clog2(rad)-1)/$clog2(rad));
      $display("Radix: %d: Num: %d NumLevels: %0d", rad, i, levels);
    end
  end





// // outputs are on the last level
// for (genvar i = 0; unsigned'(i) < Radix*NumRouters; i++) begin : gen_outputs
//   if (i < NumOut) begin : gen_connect
//     assign data_o[j]  = out_router_data[NumLevels-1][j/Radix][j%Radix].payload;
//     assign idx_o[j]   = out_router_data[NumLevels-1][j/Radix][j%Radix].inp_idx;
//     assign valid_o[j] = out_router_valid[NumLevels-1][j/Radix][j%Radix];
//     assign out_router_ready
//   end else begin : gen_tie_off

//   end
// end

  // Assertions
  // Make sure that the handshake and payload is stable
  // pragma translate_off
  `ifndef VERILATOR
  default disable iff rst_ni;
  for (genvar i = 0; unsigned'(i) < NumInp; i++) begin : gen_sel_assertions
    assert property (@(posedge clk_i) (valid_i[i] |-> sel_i[i] < sel_oup_t'(NumOut))) else
        $fatal(1, "Non-existing output is selected!");
  end

  if (AxiVldRdy) begin : gen_handshake_assertions
    for (genvar i = 0; unsigned'(i) < NumInp; i++) begin : gen_inp_assertions
      assert property (@(posedge clk_i) (valid_i[i] && !ready_o[i] |=> $stable(data_i[i]))) else
          $error("data_i is unstable at input: %0d", i);
      assert property (@(posedge clk_i) (valid_i[i] && !ready_o[i] |=> $stable(sel_i[i]))) else
          $error("sel_i is unstable at input: %0d", i);
      assert property (@(posedge clk_i) (valid_i[i] && !ready_o[i] |=> valid_i[i])) else
          $error("valid_i at input %0d has been taken away without a ready.", i);
    end
    for (genvar i = 0; unsigned'(i) < NumOut; i++) begin : gen_out_assertions
      assert property (@(posedge clk_i) (valid_o[i] && !ready_i[i] |=> $stable(data_o[i]))) else
          $error("data_o is unstable at output: %0d Check that parameter LockIn is set.", i);
      assert property (@(posedge clk_i) (valid_o[i] && !ready_i[i] |=> $stable(idx_o[i]))) else
          $error("idx_o is unstable at output: %0d Check that parameter LockIn is set.", i);
      assert property (@(posedge clk_i) (valid_o[i] && !ready_i[i] |=> valid_o[i])) else
          $error("valid_o at output %0d has been taken away without a ready.", i);
    end
  end

  initial begin : proc_parameter_assertions
    assert (Radix inside {32'd2, 32'd4}) else $fatal(1, "Only Radix-2 and Radix-4 is supported.");
    assert (NumInp > Radix) else $fatal(1, "NumInp: %0d has to be > %0d! Use another topology!",
        NumInp, Radix);
    assert (NumOut > Radix) else $fatal(1, "NumOut: %0d has to be > %0d! Use another topology!",
        NumOut, Radix);
    assert (2**$clog2(NumRouters) == NumRouters) else
        $fatal(1, "NumRouters %0d is not power of two", NumRouters);
  end
  `endif
  // pragma translate_on
endmodule
