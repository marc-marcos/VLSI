`timescale 1ns / 1ps

module tb_decode_unit;

  // DUT interface
  reg         clk;
  reg         rst_n;
  reg         instr_valid;
  reg  [15:0] instr;
  wire        decode_done;
  wire [3:0] opcode, rd, rs, imm;
  wire hazard_stall;

  // Instantiate DUT
  decode_unit dut (
      .clk(clk),
      .rst_n(rst_n),
      .instr_valid(instr_valid),
      .instr(instr),
      .decode_done(decode_done),
      .opcode(opcode),
      .rd(rd),
      .rs(rs),
      .imm(imm),
      .hazard_stall(hazard_stall)
  );

  // Clock generation: 10ns period
  initial clk = 0;
  always #5 clk = ~clk;

  // Directed test sequence
  initial begin
    integer i;

    // Initialize inputs
    rst_n = 0;
    instr_valid = 0;
    instr = 16'h0000;

    $display("[%0t] STARTING SIMULATION ...", $time);

    // Apply reset
    #5;
    @(posedge clk);
    rst_n = 1;
    @(posedge clk);
    $display("[%0t] TEST #1: Reset released, outputs should be 0", $time);

    // Decode instruction without hazard
    instr = 16'h1234;  // opcode=1, rd=2, rs=3, imm=4
    instr_valid = 1;
    @(posedge clk);
    instr_valid = 0;
    // Wait for decode_done
    repeat (3) @(posedge clk);
    $display("[%0t] TEST #2: decode_done=%b, opcode=%0h, rd=%0h, rs=%0h, imm=%0h", $time,
             decode_done, opcode, rd, rs, imm);

    // Decode instruction with hazard (rs == last_rd)
    instr = 16'h3A20;  // opcode=3, rd=A, rs=2 (matches previous rd), imm=0
    instr_valid = 1;
    @(posedge clk);
    instr_valid = 0;
    // Stall should assert
    @(posedge clk);
    $display("[%0t] TEST #3: hazard_stall=%b", $time, hazard_stall);

    // Wait for stall to clear and decode to complete
    repeat (4) @(posedge clk);
    $display("[%0t] TEST #4: decode_done=%b, opcode=%0h, rd=%0h, rs=%0h, imm=%0h", $time,
             decode_done, opcode, rd, rs, imm);

    // Decode instruction after hazard clears
    instr = 16'h4B21;  // opcode=4, rd=B, rs=2 (no hazard with last_rd=A), imm=1
    instr_valid = 1;
    @(posedge clk);
    instr_valid = 0;
    repeat (3) @(posedge clk);
    $display("[%0t] TEST #5: decode_done=%b, opcode=%0h, rd=%0h, rs=%0h, imm=%0h", $time,
             decode_done, opcode, rd, rs, imm);

    // Finish
    #20;
    $display("[%0t] TEST COMPLETE.", $time);
    $finish;
  end

  // INSERT ASSERTIONS BELOW

  /*
    ##### Assertion plan #####
    - if instr_valid and hazard_stall the opcode, rd, rs and imm have to be the certain bits of instr
    - if acceptance in cycle N then decode_done must assert in cycle N+2
    - decode_done must be a single cycle pulse
    - hazard stall if $past(rd) == rs
    - if hazard stall then no acceptance
    - if hazard stall then no decode_done assertion
    - if instr_valid and hazard_stall then the decode fields must retain their previous values and only update when instruction is acccepted
    - if back-to-back instructions with no hazard decode_done does consecutive pulses
    - when rst_n=0 all outputs must be 0 no instruction is accepted or completed until reset is released
  */

  // Assertion 1

  sequence s_acceptance; (dut.instr_valid && !dut.hazard_stall); endsequence

  property acceptance;
    s_acceptance |=> (opcode == instr[15:12] && rd == instr[11:8] && rs == instr[7:4] && imm == instr[3:0])
  endproperty

  check_acceptance :
  assert property (acceptance);

  // Assertion 2

  property decode_done;
      s_acceptance |=> ##2 (decode_done == 1'b1);
  endproperty

  check_decode_done :
  assert property (decode_done);

  // Assertion 3

  sequence s_hazard; (rs == $past(rd)); endsequence;

  property hazard;
      s_hazard |=> dut.hazard_stall;
  endproperty

  check_hazard :
  assert property (hazard);

  // Assertion 4


  // Assertion 5


  // Assertion 6

  sequence s_reset; (!dut.rst_n); endsequence

  property reset;
    s_reset |=> (dut.decode_done == 1'b0 && opcode == 4'b0 &&
                 rd == 4'b0 && rs == 4'b0 && imm == 4'b0);
  endproperty

  check_reset :
  assert property (reset);

endmodule

