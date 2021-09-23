`define W 16
`define PD `W-1:0

module cnt(
  input clk, input rst, input [`PD] inp, input en,
  output reg [`PD] base, output reg [`PD] addr, output reg[`PD] cnt );

always @(posedge clk) begin
  if(rst) begin
    base <= 0;
    addr <= 0;
    cnt <= 0;
  end else begin
    base <= en ? inp : base;
    addr <= en ? inp : addr + 1;
    cnt <= en ? 0 : cnt + 1;
  end
end

assert property (! ( base == (`W'b1 << (`W-1)) && addr == 1 && cnt == 1 ) );


endmodule
