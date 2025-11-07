`timescale 1ns/1ps

module alu_4bit_tb;

  // Shared signals (inputs)
  logic [3:0] A;
  logic [3:0] B;
  logic [2:0] op;

  // Golden model signals
  logic [3:0] Y_golden;
  logic carry_golden;

  // Dut signals
  logic [3:0] Y_dut;
  logic carry_dut;

  alu_4bit_v0 dut (
    .A(A),
    .B(B),
    .op(op),
    .Y(Y_dut),
    .carry(carry_dut)
  );

  golden_model golden_model (
      .A(A),
      .B(B),
      .op(op),
      .Y(Y_golden),
      .carry(Y_carry)
    );

    initial begin
      generator gen;
      gen = new();

      int error_count = 0;
      int test_count = 1000;

      $display("--- Starting Self-Checking Test (running %0d tests) ---", test_count);

      repeat (test_count) begin
        gen.randomize()

        A = gen.A;
        B = gen.B;
        op = gen.op;
        
        #1;

        if (Y_golden != Y_dut || carry_golden != carry_dut) begin
          $error("--- MISMATCH DETECTED ---");
          gen.display("GEN");
          $display("  [DUT] Y=0x%h (%0d), Carry=%b", dut_Y, dut_Y, dut_carry);
          golden_model.display();
          error_count++;
        end
      end

      if (error_count == 0) begin
        $display("--- TEST PASSED: All %0d random tests passed. ---", test_count);
      end else begin
        $display("--- TEST FAILED: %0d mismatches found in %0d tests. ---", error_count, test_count);
      end

      $finish;
    end



endmodule

// Can't modify code from alu_4bit so I declare it here and call it directly
// with its signals
function void display(string prefix = "DUT");
  $display("[%s] A=0x%h, B=0x%h, op=0b%b  =>  Y=0x%h, Carry=%b",
            prefix, A, B, op, Y, carry);
endfunction
