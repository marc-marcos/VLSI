`timescale 1ns/1ps

class Transaction;
    logic rst_n;
    logic wr_en;
    logic [4:0] wr_addr;
    logic [15:0] wr_data;
    logic [4:0] rd_addr1;
    logic [4:0] rd_addr2;

    function new();
    endfunction: new
endclass: Transaction

class Generator;
    rand logic rst_n;
    rand logic wr_en;
    rand logic [4:0] wr_addr;
    rand logic [15:0] wr_data;
    rand logic [4:0] rd_addr1;
    rand logic [4:0] rd_addr2;

    function new();
    endfunction: new
endclass: Generator

interface regfile_driver_if ();
    logic clk;
    logic rst_n;
    logic wr_en;
    logic err;
    logic [4:0] wr_addr;
    logic [15:0] wr_data;
    logic [4:0] rd_addr1;
    logic [4:0] rd_addr2;
    logic [15:0] rd_data1;
    logic [15:0] rd_data2;

    modport MONITOR (
        output rst_n;
        output clk;
        output wr_en;
        output wr_addr;
        output wr_data;
        output rd_addr1;
        output rd_addr2;
        output rd_data1;
        output rd_data2;
        output err;
    );

    modport REGFILE (
        output rst_n;
        output clk;
        output wr_en;
        output wr_addr;
        output wr_data;
        output rd_addr1;
        output rd_addr2;
        input rd_data1;
        input rd_data2;
        input err;
    );

    modport DRIVER (
        input rst_n;
        input clk;
        input wr_en;
        input wr_addr;
        input wr_data;
        input rd_addr1;
        input rd_addr2;
        input rd_data1;
        input rd_data2;
        input err;
    );
endinterface

module Driver;
endmodule: Driver

module Monitor;
endmodule: Monitor

module ScoreBoard(
    input logic clk,
    input logic rst_n,
    input logic wr_en,
    input logic [4:0] wr_addr,
    input logic [15:0] wr_data,
    input logic [4:0] rd_addr1,
    input logic [4:0] rd_addr2,
    input logic [15:0] dut_rd_data1,
    input logic [15:0] dut_rd_data2,
    input logic dut_err
);

endmodule: ScoreBoard;

module GoldenModel(
    input logic clk,
    input logic rst_n,
    input logic wr_en,
    input logic [4:0] wr_addr,
    input logic [15:0] wr_data,
    input logic [4:0] rd_addr1,
    input logic [4:0] rd_addr2,
    output logic err,
    output logic [15:0] rd_data1,
    output logic [15:0] rd_data2,
);

    logic [15:0] data [31:0];

    always_comb begin : read
        if (rd_addr1 == rd_addr2) begin
            rd_data1 = 16'hXXXX;
            rd_data2 = 16'hXXXX;
            er = 1'b1;
        end else begin
            rd_data1 = data[rd_addr1];
            rd_data2 = data[rd_addr2];
        end
    end

endmodule: GoldenModel;

module tb_regfile;

    // TO FILL BY THE STUDENT

endmodule
