module golden_model(
    input  logic [3:0] A,
    input  logic [3:0] B,
    input  logic [2:0] op,
    output logic [3:0] Y,
    output logic       carry
  );

  always_comb begin
    Y     = 4'b0;
    carry = 1'b0;

    case (op)
      3'b000: begin
        {carry, Y} = A + B;
      end

      3'b001: begin
        Y     = A - B;
        carry = (A < B);
      end

      3'b010: begin
        Y = A & B;
      end

      3'b011: begin
        Y = A | B;
      end

      3'b100: begin
        Y = A ^ B;
      end

      3'b101: begin
        Y = ~A;
      end

      3'b110: begin
        Y = A;
      end

      3'b111: begin
        Y = B;
      end
    endcase

    function void display(string prefix = "DUT");
      $display("[%s] A=0x%h, B=0x%h, op=0b%b  =>  Y=0x%h, Carry=%b",
                prefix, A, B, op, Y, carry);
    endfunction
  end

endmodule
