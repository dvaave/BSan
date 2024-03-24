#include <iostream>
#include <fstream>
#include <string.h>

void print_info(Dyninst::ParseAPI::Function *f,unsigned long addr, unsigned long opcode, unsigned long memread, unsigned long memwrite, unsigned long reg1, unsigned long reg2, unsigned long sdisp, unsigned long ddisp, unsigned long sireg, unsigned long direg, unsigned long ssc, unsigned long dsc, unsigned long imm, unsigned long point, unsigned long startb, unsigned long endb, unsigned long isize, unsigned long nsrc, unsigned long detect, unsigned long propa) {
	std::cout<< "\n";
	std::cout << f->name()<< "\n";
	std::map<unsigned long, int> reg_to_num;
	if(f->region()->getArch() == Arch_x86_64){
		reg_to_num = {
		{0x0, 0},
		{0x18010000, 1},
		{0x18010001, 2},
		{0x18010002, 3},
		{0x18010003, 4},
		{0x18010004, 5},
		{0x18010005, 6},
		{0x18010006, 7},
		{0x18010007, 8},
		{0x18010008, 9},
		{0x18010009, 10},
		{0x1801000a, 11},
		{0x1801000b, 12},
		{0x1801000c, 13},
		{0x1801000d, 14},
		{0x1801000e, 15},
		{0x1801000f, 16},
		{0x18010f00, 17}, 
        {0x18010f01, 18}, 
        {0x18010f02, 19}, 
        {0x18010f03, 20}, 
        {0x18010f04, 21}, 
        {0x18010f05, 22}, 
        {0x18010f06, 23}, 
        {0x18010f07, 24}, 
        {0x18010f08, 25}, 
        {0x18010f09, 26},
        {0x18010f0a, 27},
        {0x18010f0b, 28},
        {0x18010f0c, 29},
        {0x18010f0d, 30},
        {0x18010f0e, 31},
        {0x18010f0f, 32},
		};
	}else if(f->region()->getArch() == Arch_aarch64){
		reg_to_num = {
		{0x0, 0},
		{0x48010000, 2},
		{0x48010001, 3},
		{0x48010002, 4},
		{0x48010003, 5},
		{0x48010004, 6},
		{0x48010005, 7},
		{0x48010006, 8},
		{0x48010007, 9},
		{0x48010008, 10},
		{0x48010009, 11},
		{0x4801000a, 12},
		{0x4801000b, 13},
		{0x4801000c, 14},
		{0x4801000d, 15},
		{0x4801000e, 16},
		{0x4801000f, 17},
		{0x48010010, 18},
		{0x48010011, 19},
		{0x48010012, 20},
		{0x48010013, 21},
		{0x48010014, 22},
		{0x48010015, 23},
		{0x48010016, 24},
		{0x48010017, 25},
		{0x48010018, 26},
		{0x48010019, 27},
		{0x4801001a, 28},
		{0x4801001b, 29},
		{0x4801001c, 30},
		{0x4801001d, 31},
		{0x4801001e, 32},
		{0x4801001f, 33},
		{0x48010f00, 35},
		{0x48010f01, 36},
		{0x48010f02, 37},
		{0x48010f03, 38},
		{0x48010f04, 39},
		{0x48010f05, 40},
		{0x48010f06, 41},
		{0x48010f07, 42},
		{0x48010f08, 43},
		{0x48010f09, 44},
		{0x48010f0a, 45},
		{0x48010f0b, 46},
		{0x48010f0c, 47},
		{0x48010f0d, 48},
		{0x48010f0e, 49},
		{0x48010f0f, 50},
		{0x48010f10, 51},
		{0x48010f11, 52},
		{0x48010f12, 53},
		{0x48010f13, 54},
		{0x48010f14, 55},
		{0x48010f15, 56},
		{0x48010f16, 57},
		{0x48010f17, 58},
		{0x48010f18, 59},
		{0x48010f19, 60},
		{0x48010f1a, 61},
		{0x48010f1b, 62},
		{0x48010f1c, 63},
		{0x48010f1d, 64},
		{0x48010f1e, 65},
		{0x48010f1f, 66},
		};
	}
	std::map<unsigned long, unsigned long> opc_to_dyrio {
		{0x8, 0x30},{0x1e1, 0x12},{0x12b, 0x38},{0x237, 0xa},{0x20, 0x2a},{0x10d, 0x3d},{0x2f, 0x46},{0x10e, 0x4b},
	};
	
	int src_reg_num = reg_to_num[reg1];
	if (src_reg_num > 16) {
		src_reg_num -= 16;
	}

	int dst_reg_num = reg_to_num[reg2];
    if (dst_reg_num > 16) {
        dst_reg_num -= 16;
    }
	FILE *ofp = fopen("opt.txt", "a");
	fprintf(ofp, "0x%lx 0x%lx 0x%lx 0x%lx 0x%lx 0x%lx 0x%lx 0x%lx 0x%lx 0x%lx 0x%lx 0x%lx 0x%lx 0x%lx 0x%lx 0x%lx 0x%lx 0x%lx 0x%lx 0x%lx\n", addr, opcode, src_reg_num, dst_reg_num, sdisp, ddisp, sireg, direg, ssc, dsc, imm, point, memread, memwrite, startb, endb, isize, nsrc, detect, propa);
	fclose(ofp);

}
