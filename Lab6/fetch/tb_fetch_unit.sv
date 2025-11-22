`timescale 1ns / 1ps

module tb_fetch_unit;

  // DUT interface signals
  reg         clk;
  reg         rst_n;
  reg         pc_en;
  reg         branch_en;
  reg  [ 7:0] branch_addr;
  wire [15:0] instr;

  // Instantiate DUT
  fetch_unit dut (
      .clk        (clk),
      .rst_n      (rst_n),
      .pc_en      (pc_en),
      .branch_en  (branch_en),
      .branch_addr(branch_addr),
      .instr      (instr)
  );

  // Clock generation: 10ns period
  initial clk = 0;
  always #5 clk = ~clk;

  // Directed test sequence
  initial begin
    integer i;

    // Initialize inputs
    clk         = 0;
    rst_n       = 0;
    pc_en       = 0;
    branch_en   = 0;
    branch_addr = 8'h00;

    $display("[%0t] STARTING SIMULATION ...", $time);

    // Apply reset
    #5;
    @(posedge clk);
    rst_n = 1;
    @(posedge clk);
    $display("[%0t] TEST #1: Reset released, pc should be 0, instr=%0d", $time, instr);

    // Sequential pc increments
    pc_en = 1;
    for (i = 1; i <= 4; i = i + 1) begin
      @(posedge clk);
      $display("[%0t] TEST #%1d: pc increment, pc=%0h, instr=%0d", $time, i, dut.pc, instr);
    end
    pc_en = 0;

    // Branch test
    branch_addr = 8'h10;
    branch_en = 1;
    @(posedge clk);
    branch_en = 0;
    $display("[%0t] TEST #5: Branch taken to addr=0x%0h, pc=%0h, instr=%0d", $time, branch_addr,
             dut.pc, instr);

    // Branch priority over pc_en
    branch_addr = 8'h20;
    pc_en       = 1;
    branch_en   = 1;
    @(posedge clk);
    branch_en = 0;
    pc_en     = 0;
    $display("[%0t] TEST #6: Branch priority test, pc should be 0x20, instr=%0d", $time, instr);

    // No control signals
    @(posedge clk);
    $display("[%0t] TEST #7: No control active, pc=%0h, instr=%0d", $time, dut.pc, instr);

    // End simulation
    #20;
    $display("[%0t] TEST COMPLETE.", $time);
    $finish;
  end

  // INSERT ASSERTIONS BELOW


  // Assertion 1

  sequence s_reset; (!dut.rst_n); endsequence

  property reset_behavior;
    s_reset |=> (pc == 0);
  endproperty

  check_reset_behavior :
  assert property (reset_behavior);

  // Assertion 2

  sequence s_branch; (dut.branch_en); endsequence

  property branch_priority;
    s_branch |=> (pc == $past(
        dut.branch_addr
    ));
  endproperty

  check_branch_priority :
  assert property (branch_priority);

  // Assertion 3

  sequence s_pc_en_no_branch; (!dut.branch_en && dut.pc_en); endsequence

  property pc_increment;
    s_pc_en_no_branch |=> (pc == $past(
        pc
    ) + 2);
  endproperty

  check_pc_increment :
  assert property (pc_increment);

  // Assertion 4

  sequence s_enables_idle; (!dut.branch_en && !dut.pc_en); endsequence

  property stable_pc;
    s_enables_idle |=> (pc == $past(
        pc
    ));
  endproperty

  check_stable_pc :
  assert property (stable_pc);

  // Assertion 5

  property instruction_consistency;
    dut.instr == dut.mem[pc];
  endproperty

  check_instruction_consistency :
  assert property (instruction_consistency);

  // Assertion 6

  property pc_inside_range;
    dut.pc inside {[0 : 255]};
  endproperty

  check_pc_inside_range :
  assert property (pc_inside_range);


endmodule

