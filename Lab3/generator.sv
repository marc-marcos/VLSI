class generator;

  rand logic [3:0] A;
  rand logic [3:0] B;
  rand logic [2:0] op;

  function new();
  endfunction

  function void display(string prefix = "GEN");
    $display("[%s] A=0x%h, B=0x%h, op=0b%b", prefix, A, B, op);
  endfunction

endclass
