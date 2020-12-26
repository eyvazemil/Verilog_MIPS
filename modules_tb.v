module testbench();
	reg         clk;
	reg         reset;
	wire [31:0] data_to_mem, address_to_mem;
	wire        memwrite;

	top simulated_system (clk, reset, data_to_mem, address_to_mem, write_enable);

	initial	begin
		$dumpfile("test");
		$dumpvars;
		reset<=1; # 2; reset<=0;
		#250; $finish;
	end

	// generate clock
	always	begin
		clk<=1; # 1; clk<=0; # 1;
	end
endmodule