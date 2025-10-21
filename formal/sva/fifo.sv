// Copyright © 2025 Muhammad Hayat, 10xEngineers.

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://www.apache.org/licenses/LICENSE-2.0

// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and limitations under the License.

module fifo
  #(parameter DEPTH_BITS = 3,
    parameter DATA_WIDTH = 8
    )
   (
    input  wire                   clk,
    input  wire                   resetn,
    input  wire                   push_i,
    input  wire                   pop_i,
    input  wire [DATA_WIDTH-1:0]  data_i,
    output wire                   empty_o,
    output wire                   full_o,
    output wire [DATA_WIDTH-1:0]  data_o
    );

   localparam DEPTH_MAX = 1 << DEPTH_BITS;

   reg [DATA_WIDTH-1:0] data  [DEPTH_MAX-1:0];

   reg                           empty;

   reg [DEPTH_BITS-1:0]          wptr;
   reg [DEPTH_BITS-1:0]          rptr;

   reg [DATA_WIDTH-1:0]          data_int;

   wire [DEPTH_BITS-1:0] nxt_wptr  = wptr + push_i;
   wire [DEPTH_BITS-1:0] nxt_rptr  = rptr + pop_i;

  always @(posedge clk)
       if (push_i)
         data[wptr] <= data_i;


   wire  nxt_empty = (empty || pop_i) && !push_i && (nxt_rptr == nxt_wptr);

  always @(posedge clk or negedge resetn)
    if (!resetn)
      begin
        empty <= 1'b1;
        wptr  <= {DEPTH_BITS{1'b0}};
        rptr  <= {DEPTH_BITS{1'b0}};
      end
    else
      begin
        empty <= nxt_empty;
        wptr  <= nxt_wptr;
        rptr  <= nxt_rptr;
      end

  //  always @(posedge clk)
  //    if (pop_i)
  //      data_int <= data[rptr];

   wire   full    = !empty && (rptr == wptr);

   assign empty_o = empty;
   assign full_o  = full;

  //  assign data_o  = data_int;
  assign data_o  = data[rptr];

// ----------------------Assumptions Started----------------
    // a1_full: // Do not push when full unless pop is also high
    // assume property(full_o |-> !push_i || pop_i);
    // a2_empty: // Do not pop data when empty_o is high.
    // assume property(empty_o |-> !pop_i);
// ----------------------Assumptions Ended------------------

endmodule
