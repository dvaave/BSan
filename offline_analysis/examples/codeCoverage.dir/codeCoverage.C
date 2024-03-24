// Example ParseAPI program; produces a graph (in DOT format) of the
// control flow graph of the provided binary.
//
// Improvements by E. Robbins (er209 at kent dot ac dot uk)

#include "CFG.h"
#include "CodeObject.h"
#include <sstream>
#include <string>
#include <unordered_set>
#include <vector>
#include "InstructionDecoder.h"
#include <iostream>
#include "Operand.h"
#include "Operand.h"
#include <iostream>
#include <set>
#include "meta.h"
#include <time.h>
#include "Instruction.h"
#include "Absloc.h"
#include "AbslocInterface.h"
#include "record.h"
#include <algorithm>
#include "passjson.h"

#define DEBUG 0
#define INFO 1

namespace dp = Dyninst::ParseAPI;
namespace st = Dyninst::SymtabAPI;
using namespace std;
using namespace Dyninst::ParseAPI;
using namespace Dyninst::SymtabAPI;
using namespace Dyninst::InstructionAPI;
char *funcname;
std::unordered_set<Dyninst::Address> pseen;
std::unordered_set<Dyninst::Address> seenregs;
std::unordered_set<Dyninst::Address> seenblocks;
mht *ht0;
mht *ht1;
mht *ht2;
mht *ht3;
reHashTable rht;
std::set<Dyninst::MachRegister> savereg;
FILE * fp, *insp;

unsigned long curr_point_f, prev_point_f,instru_count_f, detect_opt_f, propa_opt_f, totalcount_f;
unsigned long instru_count_app, detect_opt_app, propa_opt_app, totalcount_app, best_detectfaddr, best_propafaddr, best_instrufaddr;
double best_detectopt, best_propaopt, best_instruopt;
char *best_detectfunc, *best_propaofunc, *best_instrufunc;

mkv* traceback(Dyninst::ParseAPI::Function *f, dp::Block *b, Dyninst::Address entryaddr, int procheck,
Dyninst::InstructionAPI::InstructionDecoder decoder, bool initial, bool firstrace);

void operand_analysis(Dyninst::ParseAPI::Function *f, dp::Block *b, Dyninst::InstructionAPI::InstructionDecoder decoder,mkv *bobj,
Dyninst::InstructionAPI::Instruction ins, Dyninst::Address ins_addr, int pcheck, bool pout, bool jsondata, 
unsigned long* reg1, unsigned long* reg2, unsigned long* sdisp, unsigned long* ddisp, unsigned long* sireg, 
unsigned long* direg, unsigned long* ssc, unsigned long* dsc, unsigned long* imm, unsigned long* nsrc);

unsigned long getinsize(Dyninst::ParseAPI::Function *f, dp::Block *b, 
Dyninst::InstructionAPI::InstructionDecoder decoder,Dyninst::Address ins_addr);

struct loopinfo{
	int echo;
	vector<dp::Block*> lpb;
	vector<dp::Block*> lpentry;
	bool lpy;
};
std::map<unsigned long, long> regoffset;

set<Address> choose_points_to_cover_regions(set<Address> points, vector<pair<Address, Address>> regions) {
	vector<pair<Address, int>> sorted_regions;

    // Count the number of regions covered by each point
    for (Address p : points) {
        int count = 0;
        for (auto r : regions) {
            if (p >= r.first && p <= r.second) {
                count++;
            }
        }
        sorted_regions.push_back(make_pair(p, count));
    }

    // Sort the points by the number of regions they cover
    sort(sorted_regions.begin(), sorted_regions.end(),
         [](pair<Address, int> a, pair<Address, int> b) { return a.second > b.second; });

    set<pair<Address, Address>> uncovered_regions = set<pair<Address, Address>>(regions.begin(), regions.end());
    set<Address> chosen_points;

    // Choose the points that cover the most regions while keeping the size of the set minimum
    for (auto r : sorted_regions) {
        if (uncovered_regions.empty()) {
            break;
        }

        bool is_covered = false;
        for (auto it = uncovered_regions.begin(); it != uncovered_regions.end();) {
            if (r.first >= it->first && r.first <= it->second) {
                chosen_points.insert(r.first);
                for (auto reg_it = uncovered_regions.begin(); reg_it != uncovered_regions.end();) {
                    if (r.first >= reg_it->first && r.first <= reg_it->second) {
                        reg_it = uncovered_regions.erase(reg_it);
                    } else {
                        reg_it++;
                    }
                }
                is_covered = true;
                break;
            } else {
                it++;
            }
        }

        if (!is_covered && chosen_points.empty()) {
            chosen_points.insert(r.first);
        }
    }

    return chosen_points;
}

reNode* forward(Dyninst::ParseAPI::Function *f, dp::Block *b, Dyninst::InstructionAPI::InstructionDecoder decoder,Dyninst::Address ins_addr, MachRegister reg, bool use, bool mod){
	Dyninst::InstructionAPI::Instruction instr;
    //Dyninst::Address firstAddr = b->start();
    Dyninst::Address lastAddr = b->end();
    //MachRegister sreg, dreg;
	reNode* p = NULL;

	instr = decoder.decode((unsigned char *)f->isrc()->getPtrToInstruction(ins_addr));
	ins_addr += instr.size();
	
	while(ins_addr < lastAddr){
		instr = decoder.decode((unsigned char *)f->isrc()->getPtrToInstruction(ins_addr));
		if(use){
			p = getuse(rht, ins_addr, reg);
			if(p != NULL){
				return p;
			}
		}else if(mod){
			p = getlastmod(rht, ins_addr, reg);
			if(p != NULL){
                return p;
            }
		}
		ins_addr += instr.size();
	}
	return NULL;
}


reNode* backword(Dyninst::ParseAPI::Function *f, dp::Block *b, Dyninst::InstructionAPI::InstructionDecoder decoder,Dyninst::Address ins_addr, MachRegister reg, bool use, bool mod){
	Dyninst::InstructionAPI::Instruction instr;
    Dyninst::Address firstAddr = b->start();
    Dyninst::Address lastAddr = b->end();
    reNode* p = NULL;

    instr = decoder.decode((unsigned char *)f->isrc()->getPtrToInstruction(ins_addr));	
	unsigned long size;
    size = getinsize(f, b, decoder, ins_addr);
	if((ins_addr - size) >= firstAddr){
		ins_addr -= size;
	}
	while(ins_addr >= firstAddr && ins_addr < lastAddr){
		instr = decoder.decode((unsigned char *)f->isrc()->getPtrToInstruction(ins_addr));
        if(use){
            p = getuse(rht, ins_addr, reg);
            if(p != NULL){
                return p;
            }
        }else if(mod){
            p = getlastmod(rht, ins_addr, reg);
            if(p != NULL){
                return p;
            }
        }
		size = getinsize(f, b, decoder, ins_addr);
        if(size == 0){
            break;
        }
		ins_addr -= size;
	}
	return NULL;
}


vector<pair<Address, Address>> getregion(Dyninst::ParseAPI::Function *f, dp::Block *b, reNode* lastmod, reNode* firstmod, reNode* lastuse, reNode* firstuse, bool numsrc, int memaccess, vector<pair<Address, Address>> insregion){
	Dyninst::Address bs = b->start();
	Dyninst::Address be = b->lastInsnAddr();
	Dyninst::Address lm, fm, lu, fu;
	lm = fm = lu = fu = 0;

	if(numsrc){
		if(memaccess == 0){
			if(lastuse == NULL){
				lu = bs;
			}else{
				lu = lastuse->redata.startaddr;
			}
			if(firstuse == NULL){
				fu = be;
			}else{
				fu = firstuse->redata.startaddr;
			}
			insregion.push_back(make_pair(lu, fu));
		}else{
			if(lastmod == NULL){
				lm = bs;	
			}else{
				lm = lastmod->redata.startaddr;
			}
			if(firstmod == NULL){
				fm = be;
			}else{
				fm = firstmod->redata.startaddr;
			}
			insregion.push_back(make_pair(lm, fm));
		}
	}else{
		if(lastuse == NULL){
            lu = bs;
        }else{
            lu = lastuse->redata.startaddr;
        }
        if(firstuse == NULL){
            fu = be;
        }else{
            fu = firstuse->redata.startaddr;
        }
		if(lastmod == NULL){
            lm = bs;    
        }else{
            lm = lastmod->redata.startaddr;
        }
        if(firstmod == NULL){
            fm = be;
        }else{
            fm = firstmod->redata.startaddr;
        }
		insregion.push_back(make_pair(max(lm,lu), min(fm, fu)));
	}
	return insregion;

}


void getinstru(Dyninst::ParseAPI::Function *f, dp::Block *b, 
	Dyninst::InstructionAPI::InstructionDecoder decoder){
	//for now this is only for one basic block
	Dyninst::InstructionAPI::Instruction instr, inn;
	Dyninst::Address firstAddr = b->start();
	Dyninst::Address lastAddr = b->end();
	unsigned long sreg, dreg, sdisp, ddisp, sireg, direg, ssc, dsc, imm, nsrc;
	//sreg = dreg = sdisp = ddisp = sireg = direg = ssc = dsc = imm = nsrc = 0;
	reNode *slastuse, *sfirstuse, *slastmod, *sfirstmod;
	reNode *dlastuse, *dfirstuse, *dlastmod, *dfirstmod;
	Dyninst::Address hb, lb;
	vector<pair<Address, Address>> regions;
	set<Address> insad;
	set<Address> goodloc;
	map<Dyninst::Address, Dyninst::Address> insmap;
	map<Dyninst::Address, Dyninst::Address>::iterator iter;
	string opco, sopd, dopd;
	std::set<Expression::Ptr> aaa;
	Dyninst::InstructionAPI::Expression::Ptr src;
    Dyninst::InstructionAPI::Expression::Ptr dest;
	std::vector<Expression::Ptr> kid1, kid2;
	std::vector <Dyninst::InstructionAPI::Operand > opds;
	std::set<MachRegister> checked_reg;
	std::set<MachRegister> zero_reg;
	mkv* bbbb = (mkv*)calloc(1,sizeof(mkv));
	regions.clear();
	insad.clear();
	goodloc.clear();
	checked_reg.clear();
	zero_reg.clear();
	bbbb->creg = checked_reg;
	bbbb->zreg = zero_reg;
	while(firstAddr < lastAddr){
		instr = decoder.decode((unsigned char *)f->isrc()->getPtrToInstruction(firstAddr));
		insad.insert(firstAddr);
		reNode *p = research(rht, firstAddr);
		if(p != NULL){
			if(p->redata.numsrc){
				if(p->redata.memaccess == 0){
					//means num->reg(mod)
					dlastuse = backword(f, b, decoder, firstAddr, p->redata.regdst, true, false);
					dfirstuse = forward(f, b, decoder, firstAddr, p->redata.regdst, true, false);
					regions = getregion(f, b, NULL, NULL, dlastuse, dfirstuse, true, 0, regions);
				}else{
					//means num->mem(use)
					dlastmod = backword(f, b, decoder, firstAddr, p->redata.regdst, false, true);
					dfirstmod = forward(f, b, decoder, firstAddr, p->redata.regdst, false, true);
					regions = getregion(f, b, dlastmod, dfirstmod, NULL, NULL, true, p->redata.memaccess, regions);
				}
			}else{
				//means reg(use)->reg(mod), reg(use)->mem(use), mem(use)->reg(mod)
				if(p->redata.memaccess == 0 || p->redata.memaccess == 1){
					dlastuse = backword(f, b, decoder, firstAddr, p->redata.regdst, true, false);
                    dfirstuse = forward(f, b, decoder, firstAddr, p->redata.regdst, true, false);
					slastmod = backword(f, b, decoder, firstAddr, p->redata.regsrc, false, true);
                    sfirstmod = forward(f, b, decoder, firstAddr, p->redata.regsrc, false, true);
					regions = getregion(f, b, slastmod, sfirstmod, dlastuse, dfirstuse, false, p->redata.memaccess, regions);
				}else if(p->redata.memaccess == 2 || p->redata.memaccess == 3){
					// cmp reg/mem, reg/mem
					slastmod = backword(f, b, decoder, firstAddr, p->redata.regsrc, false, true);
                    sfirstmod = forward(f, b, decoder, firstAddr, p->redata.regsrc, false, true);
					dlastmod = backword(f, b, decoder, firstAddr, p->redata.regdst, false, true);
                    dfirstmod = forward(f, b, decoder, firstAddr, p->redata.regdst, false, true);
					regions = getregion(f, b, slastmod, sfirstmod, dlastmod, dfirstmod, false, p->redata.memaccess, regions);
				}
			}
		}
		firstAddr += instr.size();
	}
	goodloc = choose_points_to_cover_regions(insad, regions);
	int kk = 1;
	for(Address p : goodloc){
		int cc = 1;
		if(kk == cc){
			for (auto r : regions) {
				int zz = 1;
				if(p >= (unsigned long)r.first && p <= (unsigned long)r.second){
					//printf("%x, %lx\n", cc, p);
					for(Address q : insad){
						if(zz == cc){
							insmap.insert({q, p});
							//printf("%lx, %lx\n", q, p);
							break;
						}else{
							zz++;
						}
					}
					cc++;
				}else{
					kk = cc;
					break;
				}
			}
		}else{
			for(auto r : regions){
				int zz = 1;
				if(cc >= kk){
					if(p >= (unsigned long)r.first && p <= (unsigned long)r.second){
						//printf("%x, %lx\n", cc, p);
						for(Address q : insad){
							if(zz == cc){ 
								insmap.insert({q, p});
								//printf("%lx, %lx\n", q, p);
								break;
							}else{
								zz++;
							}
						}
						cc++;
					}else{
						kk = cc;
						break;
					}	
				}else{
					cc++;
				}
			}
		}
	}
	firstAddr = b->start();
    while(firstAddr < lastAddr){
        aaa.clear();
		opds.clear();
		kid1.clear();
		kid2.clear();
		inn = decoder.decode((unsigned char *)f->isrc()->getPtrToInstruction(firstAddr));
        entryID opc = inn.getOperation().getID();
        opco = inn.getOperation().format();
        sreg = dreg = sdisp = ddisp = sireg = direg = ssc = dsc = imm = nsrc = 0;
        //operand_analysis(f, b, decoder, inn, firstAddr, false, false, true, &sreg, &dreg,&sdisp, &ddisp, &sireg, &direg, &ssc, &dsc, &imm, &nsrc);
        //cout << "\n";
		//bool xxxx = inn.readsMemory();
		//bool yyyy = inn.writesMemory();
		unsigned long mr, mw;
		mr = mw = 0;
		inn.getOperands(opds);
		int onum = opds.size();
		if(onum == 2){
			//if(f->region()->getArch() == Arch_x86_64){
				cout << "-------------\n" << inn.format() << "-----------\n";
				operand_analysis(f, b, decoder, bbbb,inn, firstAddr, false, false, true, &sreg, &dreg,&sdisp, &ddisp, &sireg, &direg, &ssc, &dsc, &imm, &nsrc);
			//}
			
			dest = inn.getOperand(0).getValue();
			src = inn.getOperand(1).getValue();
			src->getChildren(kid1);
			dest->getChildren(kid2);
			if(kid1.size() == 1 && inn.readsMemory()){
				mr = 1;
			}else if(kid2.size() == 1 && inn.writesMemory()){
				mw = 1;
			}	
		}else if(onum == 1){
			//operand_analysis(f, b, decoder, inn, firstAddr, false, false, true, &sreg, &dreg,&sdisp, &ddisp, &sireg, &direg, &ssc, &dsc, &imm, &nsrc);
			src = dest = inn.getOperand(0).getValue();
			src->getChildren(kid1);
            dest->getChildren(kid2);
			if(kid1.size() == 1 && inn.readsMemory()){
                mr = 1;
            }else if(kid2.size() == 1 && inn.writesMemory()){
                mw = 1;
            }
		}else if(onum == 0){
			 if(inn.readsMemory()){
				mr = 1;
			 }else if(inn.writesMemory()){
				mw = 1;
			 }
		}
		iter = insmap.find(firstAddr);
		reNode* da = research(rht, firstAddr);
#if INFO
		curr_point_f = iter->second;
		if(prev_point_f != curr_point_f){
			instru_count_f ++;
			instru_count_app++;
		}
#endif
		if(da != NULL){
			print_info(f, firstAddr, (unsigned long)opc, mr, mw, sreg, dreg, sdisp, ddisp, sireg, direg, ssc, dsc, imm, iter->second, b->start(), b->end(), inn.size(), nsrc, da->redata.detect, da->redata.propa);
#if INFO
			if(da->redata.detect == 0){
				detect_opt_f ++;
				detect_opt_app ++;
			}
			if(da->redata.propa == 0){
				propa_opt_f ++;
				propa_opt_app ++;
			}
#endif
		}else{
			print_info(f, firstAddr, (unsigned long)opc, mr, mw, sreg, dreg, sdisp, ddisp, sireg, direg, ssc, dsc, imm, iter->second, b->start(), b->end(), inn.size(), nsrc, 1, 1);
		}
		firstAddr += inn.size();
#if INFO
		prev_point_f = iter->second;
		totalcount_f ++;
		totalcount_app ++;
#endif
    }
	//jsondata(f, b, decoder);
	//redestory(rht);
	free(bbbb);
}

unsigned long getinsize(Dyninst::ParseAPI::Function *f, dp::Block *b, 
	Dyninst::InstructionAPI::InstructionDecoder decoder,Dyninst::Address ins_addr){
	Dyninst::InstructionAPI::Instruction instr;
	Dyninst::Address firstAddr = b->start();
	Dyninst::Address lastAddr = b->end();
		
	if(ins_addr == f->entry()->start()){
		return 0;
	}

	while(firstAddr < lastAddr){
		instr = decoder.decode((unsigned char *)f->isrc()->getPtrToInstruction(firstAddr));
		firstAddr += instr.size();
		if(firstAddr == ins_addr){
			unsigned long size = instr.size();
			return size;
		}
	}
	
}

void maxoffsetinbb(Dyninst::ParseAPI::Function *f, dp::Block *b, Dyninst::InstructionAPI::InstructionDecoder decoder, long off1, long off2, MachRegister reg){
	unsigned long x1 = abs(off1);
	unsigned long x2 = abs(off2);
	if(x1 > x2){
		regoffset[reg] = x1;
	}else{
		regoffset[reg] = x2;
	}
}


void maxoffsetinbbs(Dyninst::ParseAPI::Function *f, dp::Block *b, Dyninst::InstructionAPI::InstructionDecoder decoder, long off1, long off2, entryID opc, MachRegister reg){
	unsigned long x1 = abs(off1);
	unsigned long x2 = abs(off2);
	if(opc == 0x20/*call*/ || opc == 0x2f/*ret*/){
		auto pos = savereg.find(reg);
		if(pos != savereg.end()){
			if(x1 > x2){
				regoffset[reg] = x1;
			}else{
				regoffset[reg] = x2;
			}
		}
	}else{
		if(x1 > x2){
			regoffset[reg] = x1;
		}else{
			regoffset[reg] = x2;
		}
	}
}

void tracepropa_bb(Dyninst::ParseAPI::Function *f, dp::Block *b, mkv *bobj,Dyninst::InstructionAPI::InstructionDecoder decoder, 
	MachRegister reg, Dyninst::Address ins_addr){
	Dyninst::InstructionAPI::Instruction instr;
	reNode* pp = NULL;
	long off1, off2;
	off1 = off2 = 0;
    //Dyninst::Address lastAddr = b->end();
    Dyninst::Address firstAddr = b->start();
	instr = decoder.decode((unsigned char *)f->isrc()->getPtrToInstruction(ins_addr));
	unsigned long size;
	size = getinsize(f, b, decoder, ins_addr);
	ins_addr -= size;
    //instr = decoder.decode((unsigned char *)f->isrc()->getPtrToInstruction(b->lastInsnAddr()));
    //cout << "\n****" << instr.format() << "\n****\n";
    while(ins_addr >= firstAddr && ins_addr < b->end()){
		if(ins_addr <= f->entry()->start()){
			return;
		}
        instr = decoder.decode((unsigned char *)f->isrc()->getPtrToInstruction(ins_addr));	
		maxoffsetinbb(f, b, decoder, off1, off2, reg);
		pp = getlastmod(rht, ins_addr, reg);
		if(pp != NULL){
			break;
		}
		size = getinsize(f, b, decoder, ins_addr);
		ins_addr -= size;
		if(size == 0){
			break;
		}
	}
	if(pp != NULL){
		reinsertpa(rht, ins_addr, 1);
		if(pp->redata.psrc){
			return;
		}
		MachRegister treg = pp->redata.regsrc;
		if(ins_addr > firstAddr){
			tracepropa_bb(f, b, bobj,decoder, treg, ins_addr);
		}else{
			for(dp::Edge *e : b->sources()){
				if(!(e->interproc())){
					dp::Block *tb = e->src();
					if (pseen.count(tb->start()) > 0){
						continue;
					}
					pseen.insert(tb->start());
					instr = decoder.decode((unsigned char *)f->isrc()->getPtrToInstruction(tb->lastInsnAddr()));
					entryID opc = instr.getOperation().getID();
					if(opc == 0x20/*call*/){
						auto pos = savereg.find(reg);
						if(pos != bobj->creg.end()){
							tracepropa_bb(f, tb, bobj,decoder, reg, tb->end());
						}else{
							break;
						}
					}else{
						tracepropa_bb(f, tb, bobj,decoder, reg, tb->end());
					}
				}
			}	
		}
	}else{
		for(dp::Edge *e : b->sources()){
            if(!(e->interproc())){
				dp::Block *tb = e->src();
				if(pseen.count(tb->start()) > 0){
                    continue;
                }
				pseen.insert(tb->start());
                instr = decoder.decode((unsigned char *)f->isrc()->getPtrToInstruction(tb->lastInsnAddr()));
                entryID opc = instr.getOperation().getID();
                maxoffsetinbbs(f, b, decoder, off1, off2, opc, reg);
				if(opc == 0x20/*call*/){
                    auto pos = savereg.find(reg);
                    if(pos != bobj->creg.end()){
                        tracepropa_bb(f, tb, bobj,decoder, reg, tb->end());
                    }else{
                        break;
                    }
                }else{
                    tracepropa_bb(f, tb, bobj,decoder, reg, tb->end());
                }
            }
        }   
    }
}

void operand_analysis(Dyninst::ParseAPI::Function *f, dp::Block *b, Dyninst::InstructionAPI::InstructionDecoder decoder,mkv *bobj,
Dyninst::InstructionAPI::Instruction ins, Dyninst::Address ins_addr, int pcheck, bool pout, bool jsondata, 
unsigned long* reg1, unsigned long* reg2, unsigned long* sdisp, unsigned long* ddisp, unsigned long* sireg, 
unsigned long* direg, unsigned long* ssc, unsigned long* dsc, unsigned long* imm, unsigned long* nsrc){
	std::set<Expression::Ptr> mem;
	Dyninst::InstructionAPI::Expression::Ptr src; 
    Dyninst::InstructionAPI::Expression::Ptr dest;
    Dyninst::InstructionAPI::Expression::Ptr pp[5];
	//pp[5] = {NULL};
	std::vector<Expression::Ptr> kid, kid1, kid2, kid3, kid4, kid5, kid6, kid7, kid8, kid0;
    InstructionAPI::Expression::Ptr baseExpr, scaleExpr, dispExpr, indexExpr;
	int path[65] = {0};
	int readcheck, writecheck; 
	readcheck = writecheck = 0;
	bool to_id = false;
	bool to_zero= false;
	bool check_base = false;
	bool zero_base = false;
	MachRegister sreg;
	MachRegister dreg;
	int access = 0;
	bool numsrc = false;
	//fp = fopen("analysis.txt", "a");
	entryID opc = ins.getOperation().getID();
	std::vector<Operand> opers;
	opers.clear();
		//printf("11111111111111111111111111111\n");
	if(opc == e_inc || opc == e_dec || opc == 0x212 || opc == 0x209 || opc == 0x20a || opc == 0x20e || opc == 0x2f || 
		opc == 0x15a || opc == 0x206 || opc == 0x203 || opc == 0x210 || opc == 0x204 || opc == 0x208 || opc == 0x205 || 
		opc == 0x20c || opc == 0x15c || opc == 0x52 || opc == 0x207 || opc == 0x20f || opc == 0xcc || opc == 0xdb ||
		opc == 0xd3){
		src = dest = ins.getOperand(0).getValue();
	}else if(opc == 0x5a || opc == 0x59 || opc == 0x408 || opc == 0x8 || opc == 0x20 || opc == 0x10e){
		//readcheck = 0;
		pcheck = 0;
		return;
	}/*else if(opc == 0x1e1){
		writecheck = 1;
	
	}else if(opc == e_pop){
		readcheck = 1;
	}*/
	/*if(opc == 0x20){
		return;
	}*/

	else{
		int zz = 0;
		dest = ins.getOperand(0).getValue();
		src = ins.getOperand(1).getValue();
		//cout << "ins "<< ins_addr<<": " <<ins.format()<<"\n";
		//cout << "dest: "<< ins.getOperand(0).format(Arch_aarch64, 0)<< "\n";
		//cout << "src: "<< ins.getOperand(1).format(Arch_aarch64, 0) << "\n";
		if(f->region()->getArch() == Arch_aarch64){
			ins.getOperands(opers);
			pp[5] = {NULL};
			for(Operand oper : opers){
				//cout << "oper "<<zz <<" : " << oper.format(Arch_aarch64, 0) << "\n";
				pp[zz] = oper.getValue();
				pp[zz]->getChildren(kid1);
				//cout << "kid  "<<zz <<" : " << kid1.size()<<"\n";
				zz++;
				kid1.clear();
			}
		}
	}
	//printf("%p, %p\n", kid1, kid2);
	if(f->region()->getArch() == Arch_x86_64){
	src->getChildren(kid1);
	dest->getChildren(kid2);
	if(kid1.size() == 1 && ins.readsMemory()){
		ins.getMemoryReadOperands(mem);
		//auto pos1 = checked_mem.find(kid1);
        //auto pos2 = zero_mem.find(kid1);
		readcheck = 1;
		//fprintf(fp, "0x%x 1 1\n", ins_addr);
		for(std::set<Expression::Ptr>::iterator ik = mem.begin();ik != mem.end();++ik){
			(*ik)->getChildren(kid);
			if(kid.size() == 2){
				Expression::Ptr check3 = kid[0];
				Expression::Ptr check4 = kid[1];
				(*check3).getChildren(kid3);
				(*check4).getChildren(kid4);
				//std::cout << "-----------12";
				if(kid3.size() == 2){
					Expression::Ptr check5 = kid3[0];
					Expression::Ptr check6 = kid3[1];
					(*check5).getChildren(kid5);
					(*check6).getChildren(kid6);
					//std::cout << "-11-";
					if(kid5.size() == 2){
						scaleExpr = kid5[1];
						indexExpr = kid5[0];
						MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(indexExpr))->getID();
#if DEBUG						
						fprintf(fp, "1-%lx %s ", reg, reg.name().c_str());
#endif
						//cout << reg.name() << "\t";
						//cout << scaleExpr->eval().convert<long>() <<"\t";
#if DEBUG
						fprintf(fp, "2-%lx ", scaleExpr->eval().convert<long>());
#endif
						//std::cout << "-10-";
					}else{
						//std::cout << "-9-";
						if(dynamic_cast<RegisterAST*>(check5.get())){
							MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(check5))->getID();
#if DEBUG							
							fprintf(fp, "3-%lx %s ", reg, reg.name().c_str());
#endif						
							if(jsondata){
								*reg1 = reg;
							}
							sreg = reg;	
							access = 1;
							auto pos1 = bobj->creg.find(reg);
							auto pos2 = bobj->zreg.find(reg);
							if(pos1 == bobj->creg.end()){
								check_base = true;
								readcheck = 1;
								//getdetect(ins_addr, readcheck);
								//getpropa(reg);
							}
							if(pos2 != bobj->zreg.end()){
								//zero_reg.erase(pos2);
								zero_base = true;
							}
							path[3] = 1;
							//cout <<"1-" <<reg << "\t";
						}else{
							//cout <<"\t"<< (check5)->eval().convert<long>();
#if DEBUG							
							fprintf(fp, "4-%lx ", (check5)->eval().convert<long>());
#endif						
						}
					}
					if(kid6.size() == 2){
						scaleExpr = kid6[1];
						indexExpr = kid6[0];
						MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(indexExpr))->getID();
#if DEBUG						
						fprintf(fp, "5-%lx %s ", reg, reg.name().c_str());
						fprintf(fp, "6-%lx ", scaleExpr->eval().convert<long>());
#endif					
						if(jsondata){
                            *sireg = reg;
							*ssc = scaleExpr->eval().convert<long>();
                        }
						sreg = reg;
						access = 1;
						auto pos1 = bobj->creg.find(reg);
                        auto pos2 = bobj->zreg.find(reg);
						if(path[3] && !check_base){
							if(zero_base){
								if(pos1 == bobj->creg.end()){
									readcheck = 1;
									//getdetect(ins_addr, readcheck);
									//getpropa(reg);
									bobj->creg.insert(reg);
								}else{
									readcheck = 0;
								}
								if(pos2 != bobj->zreg.end()){
									bobj->zreg.erase(reg);
								}
							}else{
								readcheck = 1;
								//getdetect(ins_addr, readcheck);
                                //getpropa(reg);
							}
						}
						//cout << reg.name() << "\t";
						//cout << scaleExpr->eval().convert<long>() <<"\t";
						//std::cout << "-8-";
					}else{
						//std::cout << "-7-";
						if(dynamic_cast<RegisterAST*>(check6.get())){
							MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(check6))->getID();
#if DEBUG							
							fprintf(fp, "7-%lx %s ", reg, reg.name().c_str());
#endif							
							//cout <<"2-"<<reg << "\t";
						}else{
#if DEBUG
							fprintf(fp, "8-%lx ", (check6)->eval().convert<long>());
#endif							
							//cout <<"\t"<< (check6)->eval().convert<long>();
						}
					}
				}else{
					//std::cout << "-6-";
					if(dynamic_cast<RegisterAST*>(check3.get())){
						MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(check3))->getID();
#if DEBUG						
						fprintf(fp, "9-%lx %s ", reg, reg.name().c_str());
#endif						
						sreg = reg;
						if(jsondata){
							*reg1 = reg;
						}
						access = 1;
						auto pos1 = bobj->creg.find(reg);
						auto pos2 = bobj->zreg.find(reg);
						if(pos1 == bobj->creg.end()){
							readcheck = 1;
							bobj->creg.insert(reg);
						}else{
							readcheck = 0;
						}
						if(pos2 != bobj->zreg.end()){
							bobj->zreg.erase(reg);
						}
						path[9] = 1;
					}else{
#if DEBUG						
						fprintf(fp, "10-%lx ", (check3)->eval().convert<long>());
#endif						
						//cout <<"\t"<< (check3)->eval().convert<long>();
					}
				}
				if(kid4.size() == 2){
					Expression::Ptr check7 = kid4[0];
					Expression::Ptr check8 = kid4[1];
					(*check7).getChildren(kid7);
					(*check8).getChildren(kid8);
					if(kid7.size() == 2){
						scaleExpr = kid7[1];
						indexExpr = kid7[0];
						MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(indexExpr))->getID();
#if DEBUG						
						fprintf(fp, "11-%lx %s ", reg, reg.name().c_str());
						fprintf(fp, "12-%lx ", scaleExpr->eval().convert<long>());
#endif						
						//cout <<"4-" <<reg.name() << "\t";
						//cout << scaleExpr->eval().convert<long>() <<"\t";
						//std::cout << "-5-";
					}else{
						//std::cout << "-4-";
						if(dynamic_cast<RegisterAST*>(check7.get())){
							MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(check7))->getID();
#if DEBUG							
							fprintf(fp, "13-%lx %s ", reg, reg.name().c_str());
#endif							
							if(jsondata){
								*sireg = reg;
							}
							sreg = reg;
							access = 1;
							auto pos1 = bobj->creg.find(reg);
							auto pos2 = bobj->zreg.find(reg);
							if(pos1 == bobj->creg.end()){
								readcheck = 1;
								//getdetect(ins_addr, readcheck);
                                //getpropa(reg);
								bobj->creg.insert(reg);
							}else{
								readcheck = 0;
							}
							if(pos2 != bobj->zreg.end()){
								bobj->zreg.erase(reg);
							}
							//cout <<"5-" <<reg.name() << "\t";
						}else{
#if DEBUG							
							fprintf(fp, "14-%lx ", (check7)->eval().convert<long>());
#endif							
							//cout <<"\t"<< (check7)->eval().convert<long>();
						}
					}
					if(kid8.size() == 2){
						scaleExpr = kid8[1];
						indexExpr = kid8[0];
						MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(indexExpr))->getID();
#if DEBUG					
						fprintf(fp, "15-%lx %s ", reg, reg.name().c_str());
						fprintf(fp, "16-%lx ", scaleExpr->eval().convert<long>());
#endif						
						//cout <<"6-" <<reg.name() << "\t";
						//cout << scaleExpr->eval().convert<long>() <<"\t";
						//std::cout << "-3-";
					}else{
						//std::cout << "-2-";
						if(dynamic_cast<RegisterAST*>(check8.get())){
							MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(check8))->getID();
#if DEBUG							
							fprintf(fp, "17-%lx %s ", reg, reg.name().c_str());
#endif							
							//cout <<"7-" <<reg<< "\t";
						}else{
#if DEBUG
							fprintf(fp, "18-%lx ", (check8)->eval().convert<long>());
#endif							
							if(jsondata){
								*sdisp = (check8)->eval().convert<long>();
							}
							//cout <<"\t"<< (check8)->eval().convert<long>();
						}
					}
				}else{
					//std::cout << "-1-";
					if(dynamic_cast<RegisterAST*>(check4.get())){
						MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(check4))->getID();
#if DEBUG						
						fprintf(fp, "19-%lx %s ", reg, reg.name().c_str());
#endif						
						//std::cout <<"8-" <<reg;
					}else{
						//cout <<"\t"<< (check4)->eval().convert<long>();
#if DEBUG						
						fprintf(fp, "20-%lx ", (check4)->eval().convert<long>());
#endif					
						if(jsondata){
							*sdisp = (check4)->eval().convert<long>();
						}
					}
				}
			}else{
				if(dynamic_cast<RegisterAST*>((*ik).get())){
					MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(*ik))->getID();
					sreg = reg;
					access = 1;
					auto pos1 = bobj->creg.find(reg);
                    auto pos2 = bobj->zreg.find(reg);
                    if(pos1 == bobj->creg.end()){
                        readcheck = 1; 
						//getdetect(ins_addr, readcheck);
                        //getpropa(reg);
                        bobj->creg.insert(reg);
                    }else{
                        readcheck = 0; 
                    }    
                    if(pos2 != bobj->zreg.end()){
                        bobj->zreg.erase(reg);
                    }
#if DEBUG					
					fprintf(fp, "21-%lx %s ", reg, reg.name().c_str());
#endif					
					//std::cout <<"9-"<< reg;
				}
			}
		}
    }else if(kid1.size() == 0){
		//std::cout << "-----------13";
        //fprintf(fp, "0x%x 0 1\n", ins_addr);
		Expression::Ptr check1 = src;
        if(dynamic_cast<RegisterAST*>(check1.get())){
			MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(check1))->getID();
#if DEBUG            
			fprintf(fp, "22-%lx %s ", reg, reg.name().c_str());
#endif			
			sreg = reg;
			access = 0;
			path[22] = 1;
			auto pos1 = bobj->creg.find(reg);
			auto pos2 = bobj->zreg.find(reg);
            if(pos1 != bobj->creg.end()){
				to_id = true;
            }else if(pos2 != bobj->zreg.end()){
                to_zero = true;
            }
			if(jsondata){
				*reg1 = reg;
			}
			//if(ins.writesMemory()){
				//getpropa(reg);
			//}
			//std::cout <<"10-"<< reg;
			
        }else{
			//cout <<"\t"<< (check1)->eval().convert<long>();
#if DEBUG			
			fprintf(fp, "23-%lx ", (check1)->eval().convert<long>());
#endif			
			if(jsondata){
				*imm = (check1)->eval().convert<long>();
				*nsrc = 1;
			}
			numsrc = true;
			path[23] = 1;
			to_zero = true;
			if(opc == e_add || opc == e_sub){
				pcheck = 0;
			}
        }
    }else if(kid1.size() == 2){
		//std::cout << "-LEA";
		//fprintf(fp, "0x%x 0 1\n", ins_addr);
		Expression::Ptr check1 = src;
		(check1)->getChildren(kid);
		Expression::Ptr check3 = kid[0];
		Expression::Ptr check4 = kid[1];
		(*check3).getChildren(kid3);
        (*check4).getChildren(kid4);
        //std::cout << "-----------12";
        if(kid3.size() == 2){
			Expression::Ptr check5 = kid3[0];
            Expression::Ptr check6 = kid3[1];
            (*check5).getChildren(kid5);
            (*check6).getChildren(kid6);
            //std::cout << "-11-";
            if(kid5.size() == 2){
				scaleExpr = kid5[1];
				indexExpr = kid5[0];
                MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(indexExpr))->getID();
#if DEBUG				
				fprintf(fp, "24-%lx %s ", reg, reg.name().c_str());
				fprintf(fp, "25-%lx ", scaleExpr->eval().convert<long>());
#endif                
				//cout <<"11-"<< reg<< "\t";
                //cout << scaleExpr->eval().convert<long>() <<"\t";
                //std::cout << "-10-";
            }else{
				//std::cout << "-9-";
                if(dynamic_cast<RegisterAST*>(check5.get())){
                    MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(check5))->getID();
#if DEBUG                    
					fprintf(fp, "26-%lx %s ", reg, reg.name().c_str());
#endif					
					if(jsondata){
						*reg1 = reg;
					}
					//cout <<"12-" <<reg<< "\t";
                }else{
#if DEBUG					
					fprintf(fp, "27-%lx ", (check5)->eval().convert<long>());
#endif                    
					//cout <<"\t"<< (check5)->eval().convert<long>();
                }
            }
            if(kid6.size() == 2){
				scaleExpr = kid6[1];
                indexExpr = kid6[0];
                MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(indexExpr))->getID();
#if DEBUG				
				fprintf(fp, "28-%lx %s ", reg, reg.name().c_str());
				fprintf(fp, "29-%lx ", scaleExpr->eval().convert<long>());
#endif                
				if(jsondata){
					*sireg = reg;
					*ssc = scaleExpr->eval().convert<long>();
				}
				//cout <<"13-"<< reg<< "\t";
                //cout << scaleExpr->eval().convert<long>() <<"\t";
                //std::cout << "-8-";
            }else{
				//std::cout << "-7-";
                if(dynamic_cast<RegisterAST*>(check6.get())){
					MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(check6))->getID();
#if DEBUG					
					fprintf(fp, "30-%lx %s ", reg, reg.name().c_str());
#endif                    
					//cout <<"14-"<< reg<< "\t";
                }else{
#if DEBUG					
					fprintf(fp, "31-%lx ", (check6)->eval().convert<long>());
#endif					
					//cout <<"\t"<< (check6)->eval().convert<long>();
                }
            }
        }else{
			//std::cout << "-6-";
            if(dynamic_cast<RegisterAST*>(check3.get())){
				MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(check3))->getID();
#if DEBUG                
				fprintf(fp, "32-%lx %s ", reg, reg.name().c_str());
#endif				
				sreg = reg;
				if(jsondata){
					*reg1 = reg;
				}
				access = 0;
				//std::cout <<"15-" <<reg;
            }else{
				//fprintf(fp, "33-%lx ", (check3)->eval().convert<long>());
				//cout <<"\t"<< (check3)->eval().convert<long>();
            }
        }
        if(kid4.size() == 2){
			Expression::Ptr check7 = kid4[0];
            Expression::Ptr check8 = kid4[1];
            (*check7).getChildren(kid7);
			(*check8).getChildren(kid8);
            if(kid7.size() == 2){
				scaleExpr = kid7[1];
                indexExpr = kid7[0];
                MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(indexExpr))->getID();
#if DEBUG				
				fprintf(fp, "34-%lx %s ", reg, reg.name().c_str());
				fprintf(fp, "35-%lx ", scaleExpr->eval().convert<long>());
#endif                
				//cout <<"16-"<< reg<< "\t";
                //cout << scaleExpr->eval().convert<long>() <<"\t";
                //std::cout << "-5-";
            }else{
				//std::cout << "-4-";
                if(dynamic_cast<RegisterAST*>(check7.get())){
					MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(check7))->getID();
#if DEBUG                    
					fprintf(fp, "36-%lx %s ", reg, reg.name().c_str());
#endif					
					if(jsondata){
						//*sireg = reg;
					}

					//cout <<"17-"<< reg<< "\t";
					//cout << reg.name() << "\t";
                }else{
#if DEBUG					
					fprintf(fp, "37-%lx ", (check7)->eval().convert<long>());
#endif					
					//cout <<"\t"<< (check7)->eval().convert<long>();
                }
            }
            if(kid8.size() == 2){
				scaleExpr = kid8[1];
                indexExpr = kid8[0];
                MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(indexExpr))->getID();
#if DEBUG				
				fprintf(fp, "38-%lx %s ", reg, reg.name().c_str());
				fprintf(fp, "39-%lx ", scaleExpr->eval().convert<long>());
#endif                 
				//cout <<"18-"<< reg<< "\t";
				//cout << reg.name() << "\t";
                //cout << scaleExpr->eval().convert<long>() <<"\t";
                //std::cout << "-3-";
            }else{
				//std::cout << "-2-";
                if(dynamic_cast<RegisterAST*>(check8.get())){
					MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(check8))->getID();
#if DEBUG                    
					fprintf(fp, "40-%lx %s ", reg, reg.name().c_str());
#endif					
					//cout <<"19-"<< reg<< "\t";
					//cout << reg.name() << "\t";
                }else{
#if DEBUG					
					fprintf(fp, "41-%lx ", (check8)->eval().convert<long>());
#endif                    
					if(jsondata){
						//*ssc = scaleExpr->eval().convert<long>();
					}
					//cout <<"\t"<< (check8)->eval().convert<long>();
                }
            }
        }else{
            //std::cout << "-1-";
            if(dynamic_cast<RegisterAST*>(check4.get())){
				MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(check4))->getID();
#if DEBUG                
				fprintf(fp, "42-%lx %s ", reg, reg.name().c_str());
#endif				
				//cout <<"20-"<< reg<< "\t";
				//std::cout << reg <<"---"<<reg.name();
            }else{
#if DEBUG				
				fprintf(fp, "43-%lx ", (check4)->eval().convert<long>());
#endif				
				if(jsondata){
					*sdisp = (check4)->eval().convert<long>();
				}
				//cout <<"\t"<< (check4)->eval().convert<long>();
			}
        }
		
	}
	kid.clear();
	kid1.clear();
	//kid2.clear();
	kid3.clear();
	kid4.clear();
	kid5.clear();
	kid6.clear();
	kid7.clear();
	kid8.clear();
	mem.clear();

	if((kid2.size() == 1 && ins.writesMemory()) || (kid2.size() == 1 && ins.readsMemory())){
        //ins.getMemoryWriteOperands(mem);
		//auto pos1 = checked_mem.find(kid2);
		//auto pos2 = zero_mem.find(kid2);
		//fprintf(fp, "0x%x 1 1\n", ins_addr);
		//writecheck = 1;
        if(ins.readsMemory()){
			ins.getMemoryReadOperands(mem);	
			readcheck = 1;
		}else{
			ins.getMemoryWriteOperands(mem);
			writecheck = 1;
		}
		for(std::set<Expression::Ptr>::iterator ik = mem.begin();ik != mem.end();++ik){
            (*ik)->getChildren(kid);
            if(kid.size() == 2){
                Expression::Ptr check3 = kid[0];
                Expression::Ptr check4 = kid[1];
                (*check3).getChildren(kid3);
                (*check4).getChildren(kid4);
                //std::cout << "-----------12";
                if(kid3.size() == 2){
                    Expression::Ptr check5 = kid3[0];
                    Expression::Ptr check6 = kid3[1];
                    (*check5).getChildren(kid5);
                    (*check6).getChildren(kid6);
                    //std::cout << "-11-";
                    if(kid5.size() == 2){
                        scaleExpr = kid5[1];
                        indexExpr = kid5[0];
                        MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(indexExpr))->getID();
#if DEBUG						
						fprintf(fp, "44-%lx %s ", reg, reg.name().c_str());
						fprintf(fp, "45-%lx ", scaleExpr->eval().convert<long>());                
#endif						
						//cout <<"-21-"<< reg<< "\t";
						//cout << reg.name() << "\t";
                        //cout << scaleExpr->eval().convert<long>() <<"\t";
                        //std::cout << "-10-";
                    }else{
                        //std::cout << "-9-";
                        if(dynamic_cast<RegisterAST*>(check5.get())){
                            MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(check5))->getID();
#if DEBUG                            
							fprintf(fp, "46-%lx %s ", reg, reg.name().c_str());
#endif							
							if(jsondata){
								*reg2 = reg;
							}
							dreg = reg;
							auto pos1 = bobj->creg.find(reg);
                            auto pos2 = bobj->zreg.find(reg);
                            if(pos1 == bobj->creg.end()){
                                check_base = true;
                                if(ins.writesMemory()){
									writecheck = 1;
									access = 3;
								}else{
									readcheck = 1;
									access = 2;
								}
								//getdetect(ins_addr, writecheck);
                                //getpropa(reg);
                            }
                            if(pos2 != bobj->zreg.end()){
                                //zero_reg.erase(pos2);
                                zero_base = true;
                            }
                            path[46] = 1;
							//cout <<"-22-"<< reg<< "\t";
							//cout << reg.name() << "\t";
                        }else{
#if DEBUG							
							fprintf(fp, "47-%lx ",	(check5)->eval().convert<long>());
#endif                            
							//cout <<"\t"<< (check5)->eval().convert<long>();
                        }
                    }
                    if(kid6.size() == 2){
                        scaleExpr = kid6[1];
                        indexExpr = kid6[0];
                        MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(indexExpr))->getID();
#if DEBUG						
						fprintf(fp, "48-%lx %s ", reg, reg.name().c_str());
                        fprintf(fp, "49-%lx ", scaleExpr->eval().convert<long>());
#endif                        
						if(jsondata){
							*direg = reg;
							*dsc = scaleExpr->eval().convert<long>();
						}
						//if(ins.writesMemory()){
							dreg = reg;
						//}
						auto pos1 = bobj->creg.find(reg);
                        auto pos2 = bobj->zreg.find(reg);
                        if(path[46] && !check_base){
                            if(zero_base){
                                if(pos1 == bobj->creg.end()){
                                    if(ins.writesMemory()){
										writecheck = 1;
										access = 3;
									}else{
										readcheck = 1;
										access = 2;
									}
                                    bobj->creg.insert(reg);
									//getdetect(ins_addr, writecheck);
									//getpropa(reg);
                                }else{
                                    if(ins.writesMemory()){
                                        writecheck = 0; 
                                        access = 3; 
                                    }else{
                                        readcheck = 0; 
                                        access = 2; 
                                    }
									//getpropa(reg);
                                }
                                if(pos2 != bobj->zreg.end()){
                                    bobj->zreg.erase(reg);
                                }
                            }else{
                                if(ins.writesMemory()){
                                    writecheck = 1; 
                                    access = 3; 
                                }else{
                                    readcheck = 1; 
                                    access = 2; 
                                }
								//getdetect(ins_addr, writecheck);
                                //getpropa(reg);
                            }
                        }
						//cout <<"-23-"<< reg<< "\t";
						//cout << reg.name() << "\t";
                        //cout << scaleExpr->eval().convert<long>() <<"\t";
                        //std::cout << "-8-";
                    }else{
                        //std::cout << "-7-";
                        if(dynamic_cast<RegisterAST*>(check6.get())){
                            MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(check6))->getID();
#if DEBUG							
							fprintf(fp, "50-%lx %s ", reg, reg.name().c_str());
#endif                            
							//cout <<"-24-"<< reg<< "\t";
							//cout << reg.name() << "\t";
                        }else{
#if DEBUG							
							fprintf(fp, "51-%lx ", (check6)->eval().convert<long>());
#endif                            
							//cout <<"\t"<< (check6)->eval().convert<long>();
                        }
                    }
                }else{
                    //std::cout << "-6-";
                    if(dynamic_cast<RegisterAST*>(check3.get())){
                        MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(check3))->getID();
#if DEBUG						
						fprintf(fp, "52-%lx %s ", reg, reg.name().c_str());
#endif						
						/*if(path[22]){//reg->mem
							if(to_id){
								if(pos2 == zero_mem.end()){
									checked_mem.insert(kid2);
								}else{
									zero_mem.erase(pos2);
									checked_mem.insert(kid2);
								}
							}else if(to_zero){
								if(pos1 == checked_mem.end()){
                                    zero_mem.insert(kid2);
                                }else{
                                    checked_mem.erase(pos1);
                                    zero_mem.insert(kid2);
                                }
							}
						}*/
						//if(ins.writesMemory()){
							dreg = reg;
						//}
						if(jsondata){
							*reg2 = reg;
						}
						auto pos1 = bobj->creg.find(reg);
                        auto pos2 = bobj->zreg.find(reg);
                        if(pos1 == bobj->creg.end()){
                            if(ins.writesMemory()){
								writecheck = 1; 
                                access = 3; 
                            }else{
                                readcheck = 1; 
                                access = 2; 
                            }
							//writecheck = 1;
							//pcheck = 1;
                            bobj->creg.insert(reg);
							//getdetect(ins_addr, writecheck);
                            //insertpropa(ins_addr, pcheck);
                        }else{
							//pcheck = 1;
                            if(ins.writesMemory()){
                                writecheck = 0; 
                                access = 3; 
                            }else{
                                readcheck = 0; 
                                access = 2; 
                            }
							//insertpropa(ins_addr, pcheck);
                        }
                        if(pos2 != bobj->zreg.end()){
                            bobj->zreg.erase(reg);  
                        }

                        //cout <<"-25-"<< reg<< "\t";
					
						/*if(reg == 0x18010005){ 
							if(rrbp ==0){
								writecheck = 1;
								rrbp = 1;
							}else if(rrbp == 1){
								//writecheck = 0;
							}
						}else if(reg == 0x18010000){
							if(rrax == 0){
								writecheck = 1;
								rrax = 1;
							}else if(rrax == 1){
								writecheck = 0;
							}
						}*/

						//std::cout << reg <<"---"<<reg.name();
                    }else{
#if DEBUG						
						fprintf(fp, "53-%lx ", (check3)->eval().convert<long>());
#endif                        
						//cout <<"\t"<< (check3)->eval().convert<long>();
                    }
                }
                if(kid4.size() == 2){
                    Expression::Ptr check7 = kid4[0];
                    Expression::Ptr check8 = kid4[1];
                    (*check7).getChildren(kid7);
                    (*check8).getChildren(kid8);
                    if(kid7.size() == 2){
                        scaleExpr = kid7[1];
                        indexExpr = kid7[0];
                        MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(indexExpr))->getID();
#if DEBUG                        
						fprintf(fp, "54-%lx %s ", reg, reg.name().c_str());
                        fprintf(fp, "55-%lx ", scaleExpr->eval().convert<long>());
#endif						
						//cout <<"-26-"<< reg<< "\t";
						//cout << reg.name() << "\t";
                        //cout << scaleExpr->eval().convert<long>() <<"\t";
                        //std::cout << "-5-";
                    }else{
                        //std::cout << "-4-";
                        if(dynamic_cast<RegisterAST*>(check7.get())){
                            MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(check7))->getID();
#if DEBUG                            
							fprintf(fp, "56-%lx %s ", reg, reg.name().c_str());
#endif							
							if(jsondata){
								*direg = reg;
							}	
							//cout <<"-27-"<< reg<< "\t";
							//cout << reg.name() << "\t";
                        }else{
#if DEBUG							
							fprintf(fp, "57-%lx ", (check7)->eval().convert<long>());
#endif                            
							//cout <<"\t"<< (check7)->eval().convert<long>();
                        }
                    }
                    if(kid8.size() == 2){
                        scaleExpr = kid8[1];
                        indexExpr = kid8[0];
                        MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(indexExpr))->getID();
#if DEBUG                        
						fprintf(fp, "58-%lx %s ", reg, reg.name().c_str());
                        fprintf(fp, "59-%lx ", scaleExpr->eval().convert<long>());
#endif						
						//cout <<"-28-"<< reg<< "\t";
						//cout << reg.name() << "\t";
                        //cout << scaleExpr->eval().convert<long>() <<"\t";
                        //std::cout << "-3-";
                    }else{
                        //std::cout << "-2-";
                        if(dynamic_cast<RegisterAST*>(check8.get())){
                            MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(check8))->getID();
#if DEBUG                            
							fprintf(fp, "60-%lx %s ", reg, reg.name().c_str());
#endif							
							//cout <<"-29-"<< reg<< "\t";
							//cout << reg.name() << "\t";
                        }else{
#if DEBUG							
							fprintf(fp, "61-%lx ", (check8)->eval().convert<long>());
#endif                            
							if(jsondata){
								*dsc = (check8)->eval().convert<long>();
							}
							//cout <<"\t"<< (check8)->eval().convert<long>();
                        }
                    }
                }else{
                    //std::cout << "-1-";
                    if(dynamic_cast<RegisterAST*>(check4.get())){
                        MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(check4))->getID();
#if DEBUG						
						fprintf(fp, "62-%lx %s ", reg, reg.name().c_str());
#endif                        
						//cout <<"-30-"<< reg<< "\t";
						//std::cout << reg <<"---"<<reg.name();
                    }else{
#if DEBUG						
						fprintf(fp, "63-%lx ", (check4)->eval().convert<long>());
#endif                        
						if(jsondata){
							*ddisp = (check4)->eval().convert<long>();
						}
						//cout <<"\t"<< (check4)->eval().convert<long>();
                    }
                }
            }else{
                if(dynamic_cast<RegisterAST*>((*ik).get())){
                    MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(*ik))->getID();
#if DEBUG					
					fprintf(fp, "64-%lx %s ", reg, reg.name().c_str());
#endif                    
					//cout <<"-31-"<< reg<< "\t";
					//if(ins.writesMemory()){
						dreg = reg;
					//}
					if(jsondata){
						*reg2 = reg;
					}
					auto pos1 = bobj->creg.find(reg);
                    auto pos2 = bobj->zreg.find(reg);
                    if(pos1 == bobj->creg.end()){
                        if(ins.writesMemory()){
                            writecheck = 1; 
                            access = 3; 
                        }else{
                            readcheck = 1; 
                            access = 2; 
                        }
						//pcheck = 1;
						//getdetect(ins_addr, writecheck);
                        //insertpropa(ins_addr, pcheck);
						//getpropa(reg);
                       	bobj->creg.insert(reg);
                    }else{
                        if(ins.writesMemory()){
                            writecheck = 0; 
                            access = 3; 
                        }else{
                            readcheck = 0; 
                            access = 2; 
                        }
						//pcheck = 1;
						//insertpropa(ins_addr, pcheck);
                    }
                    if(pos2 != bobj->zreg.end()){
                        bobj->zreg.erase(reg);
                    }
					/*if(reg == 0x18010005){
                        if(rrbp == 0){
                            writecheck = 1;
                            rrbp = 1;
                        }else if(rrbp == 1){
                            //writecheck = 0;
                        }
                    }else if(reg == 0x18010000){
                        if(rrax == 0){
                            writecheck = 1;
                            rrax = 1;
                        }else if(rrax == 1){
                            //writecheck = 0;
                        }
                    }*/
					//std::cout <<"\t"<< reg <<"---"<<reg.name();
                }
            }
        }
    }else if(kid2.size() == 0){
        //std::cout << "-----------13";
        //fprintf(fp, "0x%x 0 1\n", ins_addr);
		Expression::Ptr check2 = dest;
        if(dynamic_cast<RegisterAST*>(check2.get())){
            MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(check2))->getID();
#if DEBUG
			fprintf(fp, "65-%lx %s ", reg, reg.name().c_str());
#endif			
			//cout <<"-32-"<< reg<< "\t";
			dreg = reg;
			auto pos1 = bobj->creg.find(reg);
            auto pos2 = bobj->zreg.find(reg);
			/*if(path[9]){//mem->reg
				if(to_id){
					if(pos2 == zero_reg.end()){
						checked_reg.insert(reg);
					}else{
                        zero_reg.erase(pos2);
                        checked_reg.insert(reg);
                    }
                }else if(to_zero){
					if(pos1 == checked_reg.end()){
						zero_reg.insert(reg);
                    }else{
						checked_reg.erase(pos1);
                        zero_reg.insert(reg);
                    }
                }
            }*/
			if(jsondata){
				*reg2 = reg;
			}
			if(path[22]){//reg->reg
				if(to_id){
					if(pos1 == bobj->creg.end()){
						bobj->creg.insert(reg);
					}
					if(pos2 != bobj->zreg.end()){
						bobj->zreg.erase(reg);
					}
				}else if(to_zero){
					if(pos1 != bobj->creg.end()){
                        bobj->creg.erase(reg);
                    }
                    if(pos2 == bobj->zreg.end()){
                        bobj->zreg.insert(reg);
                    }
				}else{
					if(pos1 != bobj->creg.end()){
                        bobj->creg.erase(reg);
                    }else if(pos2 != bobj->zreg.end()){
                        bobj->zreg.erase(reg);
                    }
				}
			}else if(path[23]){
				if(pos1 != bobj->creg.end()){
                    bobj->creg.erase(reg);
                }
                if(pos2 == bobj->zreg.end()){
                    bobj->zreg.insert(reg);
                }
			}else{
				if(pos1 != bobj->creg.end()){
                    bobj->creg.erase(reg);
                }else if(pos2 == bobj->zreg.end()){
                    bobj->zreg.erase(reg);
				}
			}
			
        }
    }
    kid.clear();
    //kid1.clear();
    kid2.clear();
    kid3.clear();
    kid4.clear();
    kid5.clear();
    kid6.clear();
    kid7.clear();
    kid8.clear();
    mem.clear();
	if(opc == 0x1e1){
        writecheck = 1;


    }else if(opc == e_pop){
        readcheck = 1;
		//getdetect(ins_addr);
    }
#if DEBUG
	fprintf(fp, "  %p\n", ins_addr);
#endif
	//printf("00000000000000000000000000000\n");
	if(pout){
		if(ins.readsMemory()){
			reinsertde(rht, ins_addr, readcheck);
			reinsertsrc(rht, ins_addr, sreg);
			reinsertdst(rht, ins_addr, dreg);
			reinsertmema(rht, ins_addr, access);
			if(access == 1 && (opc != e_cmp && opc != 0x2b && opc != 0x22)){
				reinsertpsrc(rht, ins_addr, true);
			}
			if(readcheck == 1){
				pseen.clear();
				tracepropa_bb(f, b, bobj,decoder, sreg, ins_addr);
			}
			//readcheck = 0;
			//pcheck = 0;
			fprintf(fp, "0x%x %x %x\n", ins_addr, readcheck, pcheck);
		}else if(ins.writesMemory()){
			reinsertde(rht, ins_addr, writecheck);
			reinsertsrc(rht, ins_addr, sreg);
            reinsertdst(rht, ins_addr, dreg);
            reinsertmema(rht, ins_addr, access);
			pcheck = 1;
			reinsertpa(rht, ins_addr, pcheck);
			if(writecheck == 1){
				pseen.clear();
				tracepropa_bb(f, b, bobj,decoder, dreg, ins_addr);
			}
			if(numsrc){
				//reinsertpsrc(rht, ins_addr, true);
				reinsertnumsrc(rht, ins_addr, numsrc);
			}else{
				pseen.clear();
				tracepropa_bb(f, b, bobj,decoder, sreg, ins_addr);
			}
			//insertpropa(ins_addr, pcheck);
			//writecheck = 0;
			//pcheck = 0;
			fprintf(fp, "0x%x %x %x\n", ins_addr, writecheck, pcheck);
		}else{
			reinsertde(rht, ins_addr, 0);
			reinsertsrc(rht, ins_addr, sreg);
            reinsertdst(rht, ins_addr, dreg);
            reinsertmema(rht, ins_addr, access);
			if(numsrc){
                if(opc != e_add && opc != e_sub && opc != e_cmp && opc != 0x2b && opc != 0x22){
					reinsertpsrc(rht, ins_addr, true);
					reinsertnumsrc(rht, ins_addr, numsrc);
				}
            }
			//writecheck = 0;
			//pcheck = 0;
			fprintf(fp, "0x%x %x %x\n", ins_addr, writecheck, pcheck);
		}
		if(opc == 0x2f || opc == 0x2e){
			pseen.clear();
			tracepropa_bb(f, b, bobj,decoder, x86_64::rax, ins_addr);
			pseen.clear();
			tracepropa_bb(f, b, bobj,decoder, x86_64::rdx, ins_addr);
		}else if(opc == 0x20){
			pseen.clear();
            tracepropa_bb(f, b, bobj,decoder, x86_64::rdi, ins_addr);
			pseen.clear();
            tracepropa_bb(f, b, bobj,decoder, x86_64::rsi, ins_addr);
		}
	}
	}else if(f->region()->getArch() == Arch_aarch64){
		kid0.clear();
		bool cset = false;
		bool zset = false;
		for(int kk = 0; kk < 5; kk++){
			if(pp[kk] == NULL){
				break;
			}
			pp[kk]->getChildren(kid0);
			if(kid0.size() == 1){
				//printf("sssssss\n");
				if(ins.readsMemory()){
					ins.getMemoryReadOperands(mem);
				}else if(ins.writesMemory()){
					ins.getMemoryWriteOperands(mem);
				}
				for(std::set<Expression::Ptr>::iterator ik = mem.begin();ik != mem.end();++ik){
					(*ik)->getChildren(kid);
					//cout <<"size is " <<kid.size()<<"\n";
					if(kid.size() == 2){
						Expression::Ptr check3 = kid[0];
						Expression::Ptr check4 = kid[1];
						(*check3).getChildren(kid3);
						(*check4).getChildren(kid4);
						//printf("ddddddddddddddddd\n");
						if(kid3.size() == 2){
							scaleExpr = kid3[1];
							indexExpr = kid3[0];
							MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(indexExpr))->getID();
                       
							//printf("1-%lx %s ", reg, reg.name().c_str());
							//printf("2-%lx ", scaleExpr->eval().convert<long>());

							//cout <<"-28-"<< reg<< "\t";
							//cout << reg.name() << "\t";
							//cout << scaleExpr->eval().convert<long>() <<"\t";
						}else{
							//std::cout << "-2-";
							if(dynamic_cast<RegisterAST*>(check3.get())){
								MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(check3))->getID();
								//printf("3-%lx %s ", reg, reg.name().c_str());
								auto pos1 = bobj->creg.find(reg);
								auto pos2 = bobj->zreg.find(reg);
								if(pos1 == bobj->creg.end() && pos2 == bobj->zreg.end()){
									if(ins.readsMemory()){
										readcheck = 1;
										sreg = reg;
									}else{
										writecheck = 1;
										dreg = reg;
									}
								}else{
									readcheck = 0;
									writecheck = 0;
								}
								//cout <<"-29-"<< reg<< "\t";
								//cout << reg.name() << "\t";
							}else{
								//printf("4-%lx ", (check3)->eval().convert<long>());
								//cout <<"\t"<< (check8)->eval().convert<long>();
							}
						}
						if(kid4.size() == 2){
                            scaleExpr = kid4[1];
                            indexExpr = kid4[0];
                            MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(indexExpr))->getID();
     
                            //printf("5-%lx %s ", reg, reg.name().c_str());
                            //printf("6-%lx ", scaleExpr->eval().convert<long>());

                            //cout <<"-28-"<< reg<< "\t";
                            //cout << reg.name() << "\t";
                            //cout << scaleExpr->eval().convert<long>() <<"\t";
                        }else{
                            //std::cout << "-2-";
                            if(dynamic_cast<RegisterAST*>(check4.get())){
                                MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(check3))->getID();
                                //printf("7-%lx %s ", reg, reg.name().c_str());
                                //cout <<"-29-"<< reg<< "\t";
                                //cout << reg.name() << "\t";
                            }else{
                                //printf("8-%lx ", (check4)->eval().convert<long>());
                                //cout <<"\t"<< (check8)->eval().convert<long>();
                            }    
                        }
							
						


					}else if(kid.size() == 1){
						Expression::Ptr check1 = (*ik);
                        if(dynamic_cast<RegisterAST*>(check1.get())){
                            MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(check1))->getID();
                            //printf("9-%lx %s ", reg, reg.name().c_str());
						}
					}else{
						Expression::Ptr check1 = (*ik);
						if(dynamic_cast<RegisterAST*>(check1.get())){
                            MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(check1))->getID();
                            //printf("10-%lx %s ", reg, reg.name().c_str());                          
                            auto pos1 = bobj->creg.find(reg);
                            auto pos2 = bobj->zreg.find(reg);
                            if(pos1 == bobj->creg.end() && pos2 == bobj->zreg.end()){
                                if(ins.readsMemory()){
                                    readcheck = 1; 
                                }else{
                                    writecheck = 1; 
                                }
                            }else{
                                readcheck = 0; 
                                writecheck = 0; 
                            }
							//cout << reg.name() << "\t";
                        }else{                           
							//printf("11-%lx ", (check1)->eval().convert<long>());       
                        }
					}

				}
			}else if(kid0.size() == 0){
				
			}
			kid0.clear();
			kid.clear();
			kid3.clear();
			kid4.clear();
			mem.clear();
		}
		if(!ins.readsMemory() && !ins.writesMemory()){
			pp[0]->getChildren(kid0);
			pp[1]->getChildren(kid1);
			if(kid1.size() == 0){
				if(dynamic_cast<RegisterAST*>(pp[1].get())){
					MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(pp[1]))->getID();
					//printf("13-%lx %s ", reg, reg.name().c_str());
					sreg = reg;
					auto pos1 = bobj->creg.find(reg);
					auto pos2 = bobj->zreg.find(reg);
					if(pos1 != bobj->creg.end()){
						cset = true;
					}
					if(pos2 != bobj->zreg.end()){
						zset = true;
					}
					
				}else{
					//printf("14-%lx ", (pp[1])->eval().convert<long>());
					numsrc = true;
					zset = true;
				}
			}else if(kid1.size() == 2){

			}
			if(dynamic_cast<RegisterAST*>(pp[0].get()) && kid0.size() == 0){
                MachRegister reg = (boost::dynamic_pointer_cast<InstructionAPI::RegisterAST>(pp[0]))->getID();
                //printf("12-%lx %s ", reg, reg.name().c_str());
				dreg = reg;
				auto pos1 = bobj->creg.find(reg);
                auto pos2 = bobj->zreg.find(reg);
                if(pos1 == bobj->creg.end()){
					if(cset)
						bobj->creg.insert(reg);
				}else{
					bobj->creg.erase(reg);
				}
				if(pos2 == bobj->zreg.end()){
					if(zset)
						bobj->zreg.insert(reg);
				}else{
					bobj->zreg.erase(reg);
				}
			}
			kid0.clear();
			kid1.clear();
			if(pout){
				if(ins.readsMemory()){
					reinsertde(rht, ins_addr, readcheck);
					reinsertsrc(rht, ins_addr, sreg);
					reinsertmema(rht, ins_addr, 1);
					if(readcheck == 1){
						pseen.clear();
						tracepropa_bb(f, b, bobj,decoder, sreg, ins_addr);
					}
				}else if(ins.writesMemory()){
					 reinsertde(rht, ins_addr, writecheck);
					 reinsertdst(rht, ins_addr, dreg);
					 pcheck = 1;
					 reinsertmema(rht, ins_addr, 1);
					 reinsertpa(rht, ins_addr, pcheck);
					 if(writecheck == 1){
						pseen.clear();
						tracepropa_bb(f, b, bobj,decoder, dreg, ins_addr);
					 }
				}else{
					reinsertde(rht, ins_addr, writecheck);
					reinsertsrc(rht, ins_addr, sreg);
					reinsertdst(rht, ins_addr, dreg);
					reinsertmema(rht, ins_addr, 0);
				}
			}
		}
	}
	//fclose(fp);
}

mkv *blockanalysis(Dyninst::ParseAPI::Function *f, dp::Block *b, int procheck, Dyninst::InstructionAPI::InstructionDecoder decoder,
	std::set<Dyninst::MachRegister> creg, std::set<Dyninst::MachRegister> zreg, bool pout){
	Dyninst::InstructionAPI::Instruction instr;
	Dyninst::Address lastAddr = b->end();
    Dyninst::Address firstAddr = b->start();
	instr = decoder.decode((unsigned char *)f->isrc()->getPtrToInstruction(b->lastInsnAddr()));
	mkv *bobj = (mkv*)calloc(1, sizeof(mkv));
	//cout << "\n****" << instr.format() << "\n****\n";
	bobj->startaddr = b->start();
	bobj->creg = creg;
	bobj->zreg = zreg;
	
	//std::cout <<"analysis block: " <<b->start() << "\n";
	while(firstAddr < lastAddr){
		instr = decoder.decode((unsigned char *)f->isrc()->getPtrToInstruction(firstAddr));
		entryID opcode = instr.getOperation().getID();
		//cout << hex << opcode << "\n";
		if(f->region()->getArch() == Arch_x86_64){ 
        /*different opcode get different propagation policies*/
        if(opcode == e_mov || opcode == e_xor || opcode == 0x150/*movslq*/ ||
			opcode == 0x32c || opcode == 0x153/*movzx*/ || opcode == 0x14a/*movsd*/ || opcode == 0x319/*movapd*/ ||
            opcode == 0x323/*movdqu*/ || opcode == 0x152/*movups*/ || opcode == 0x67/*cmovnl*/ ||
            opcode == 0x65/*cmovng*/ || opcode == 0x66/*cmovnge*/ || opcode == 0x64/*cmovne*/ || opcode == 0x60/*cmove*/ ||
            opcode == 0x5f/*cmovbe*/ || opcode == 0x6d/*cmovs*/ || opcode == 0x69/*cmovns*/ || opcode == 0x14f/*movsx*/||
            opcode == 0x130/*movaps*/ || opcode == 0x62/*cmovnb*/ || opcode == 0x63/*cmovnbe*/ || opcode == 0x62/*cmovnb*/||
            opcode == 0x61/*cmovnae*/ || opcode == 0x146/*movq*/ || opcode == 0x14d/*movss*/ || opcode == 0x149/*movsd*/||
            opcode == 0x12c/*movbe*/ || opcode == 0x148/*movsb*/ || opcode == 0x131/*movd*/ || opcode == 0x31a/*vmovaps*/||
            opcode == 0x330/*vmovss*/ || opcode == 0x12f/*movapd*/ || opcode == 0x32b/*vmovq*/ || opcode == 0x13c/*movmskpd*/
            || opcode == 0x31e/*vmovdqa64*/ || opcode == 0x3f8/*vsqrtss*/ || opcode == 0x320/*vmovdqu64*/ ||
            opcode == 0x135/*movdqu*/){
				//printf("%s\n",argv[1]);
                procheck = 1; 
                operand_analysis(f, b, decoder,bobj, instr,firstAddr, procheck, pout, false, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0);
        }else if(opcode == e_lea  ||opcode == e_inc || opcode == e_dec || opcode == e_sar ||
            opcode == 0x215/*shl*/ || opcode == e_shr || opcode == 0xf7/*idiv*/ || opcode == 0x212/*setz*/ ||
            opcode == 0x209/*setnl*/ || opcode == 0x20a/*setnle*/ || opcode == 0x20e/*setnz*/ || opcode == 0x15a/*neg*/||
            opcode == 0x206/*setle*/ || opcode == 0x203/*setb*/ || opcode == 0x45d/*shlx*/ || opcode == 0x45f/*sarx*/ ||
            opcode == 0x210/*setp*/ || opcode == 0x204/*setbe*/ || opcode == 0x208/*setnbe*/ || opcode == 0x205/*setl*/||
            opcode == 0x20c/*setnp*/ || opcode == 0x45e/*shrx*/ || opcode == 0x15c/*not*/ || opcode == 0x52/*bswap*/ ||
            opcode == 0x207/*setnb*/ || opcode == 0x20f/*seto*/ || opcode == 0x408/*vzeroupper*/ || opcode == 0x1e1/*push*/||
            opcode == e_pop){
				procheck = 1; 
				operand_analysis(f, b, decoder, bobj,instr, firstAddr, procheck, pout, false, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0);
        }else if(opcode == e_add || opcode == e_sub || opcode == e_imul || opcode == 0x15d/*or*/ || 
			opcode == 0x45/*and*/ || opcode == 0x9e/*div*/ || opcode == 0x286/*vcvtsi2sd*/ || opcode == 0x335/*vmulsd*/||
            opcode == 0x24e/*vaddsd*/ || opcode == 0x405/*vxorpd*/ || opcode == 0x28f/*vcvttsd2si*/||
            opcode == 0x406/*vxorps*/ || opcode == 0x31c/*vmovdqa*/ || opcode == 0x45c/*rorx*/ || opcode == 0x4f0/*vpxor*/||
            opcode == 0x452/*andn*/ || opcode == 0x1f1/*ror*/ || opcode == 0x3f0/*vpxor*/ || opcode == 0x296/*vdivsd*/||
            opcode == 0x155/*mul*/ || opcode == 0x1fd/*sbb*/ || opcode == 0x56/*bts*/ || opcode == 0x3d/*adc*/||
            opcode == 0x459/*mulx*/ || opcode == 0x1ef/*rol*/ || opcode == 0x3fb/*vsubsd*/ || opcode == 0x252/*vandpd*/||
            opcode == 0x24f/*vaddss*/ || opcode == 0x336/*vmulss*/ || opcode == 0x54/*btc*/ || opcode == 0x55/*btr*/||
            opcode == 0x1bc/*popcnt*/ || opcode == 0x454/*blsi*/ || opcode == 0x356/*vpcmpeqd*/|| opcode == 0x287/*vcvtsi2ss*/
            || opcode == 0x288/*vcvtsi2sd*/ || opcode == 0x317/*vminsd*/ || opcode == 0x313/*vmaxsd*/ || 
            opcode == 0x297/*vdivss*/ || opcode == 0x285/*vcvtsd2ss*/ || opcode == 0x290/*vcvtss2si*/ || 
            opcode == 0x389/*vpinsrd*/ || opcode == 0x381/*vpextrd*/ || opcode == 0x234/*rep stosd*/ || 
            opcode == 0x25e/*vblendpd*/ || opcode == 0x2ad/*vfmadd132sd*/ || opcode == 0x2b1/*vfmadd213sd*/ ||
            opcode == 0x3fc/*vsubss*/ || opcode == 0x26f/**vroundsd*/ || opcode == 0x253/*vandps*/ || 
            opcode == 0x51/*rep bsr*/ || opcode == 0x318/*vminss*/ || opcode == 0x314/*vmaxss*/ || 
            opcode == 0x2b5/*vfmadd231sd*/ || opcode == 0x2dd/*vfnmadd231sd*/|| opcode == 0x2d5/*vfnmadd132sd*/||
            opcode == 0x2d9/*vfnmadd213sd*/ || opcode == 0x2c5/*vfmsub213sd*/ || opcode == 0x2c9/*vfmsub231sd*/ ||
            opcode == 0x3f7/*vsqrtsd*/ || opcode == 0xfc/*insd*/ || opcode == 0x50/*rep bsf*/ || opcode == 0xe3/*fstp*/||
            opcode == 0xd2/*fld*/ || opcode == 0xd3/*fld1*/ || opcode == 0xd6/*fmul*/ || opcode == 0xed/*fucomip*/ ||
            opcode == 0xef/*fxch*/ || opcode == 0x119/*lodsb*/ || opcode == 0xbb/*fcomip*/ || opcode == 0x456/*blsr*/ ||
            opcode == 0x411/*vpxord*/ || opcode == 0x2e9/*vfnmsub231sd*/ || opcode == 0x2c1/*vfmsub132sd*/ || 
            opcode == 0x2e5/*vfnmsub213sd*/ || opcode == 0x250/*vandnpd*/ || opcode == 0x337/*vorpd*/ ||
            opcode == 0x2e1/*vfnmsub132sd*/ || opcode == 0x338/*vorps*/ || opcode == 0x2c2/*vfmsub132ss*/||
            opcode == 0x2ae/*vfmadd132ss*/ || opcode == 0x251/*vandnps*/){
				procheck = 1; 
                operand_analysis(f, b, decoder, bobj,instr, firstAddr, procheck, pout, false, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0);
        }else if(opcode == e_test || opcode == e_cmp || opcode == 0x3ff/*vucomisd*/ || opcode == 0x267/*vcomisd*/ ||
			opcode == 0x53/*bt*/ || opcode == 0x265/*vcmpsd*/ || opcode == 0x268/*vcomiss*/ || opcode == 0x5a/*cld*/ || 
            opcode == 0x27/*rep comsb*/ || opcode == 0x59/*clc*/ || opcode == 0x2b/*cmpsw*/ || opcode == 0x200/*repnz scasb*/
            || opcode == 0x400/*vucomiss*/ || opcode == 0xbc/*fcomp*/ || opcode == 0xcc/*fimul*/ || opcode == 0xdb/*frstor*/
            || opcode == 0x448/*vrndscalesd*/ || opcode == 0x266/*vcmpss*/ || opcode == 0x447/*vrndscaless*/ ||  
			opcode == 0x240/*test*/ || opcode == 0x22/*cmpl*/){
				procheck = 0; 
                operand_analysis(f, b, decoder, bobj,instr, firstAddr, procheck, pout, false, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0);
        }else if(opcode == 0x20/*call*/){
			for(Dyninst::MachRegister reg : creg){
				auto rr = savereg.find(reg);
				if(rr == savereg.end()){
					creg.erase(reg);
				}
			}
			for(Dyninst::MachRegister reg : zreg){
                auto rr = savereg.find(reg);
                if(rr == savereg.end()){
					zreg.erase(reg);
                }
            }
			pseen.clear();
            tracepropa_bb(f, b, bobj,decoder, x86_64::rdi, firstAddr);
            pseen.clear();
            tracepropa_bb(f, b, bobj,decoder, x86_64::rsi, firstAddr);
			/*getpropa(x86_64::rdi);
			getpropa(x86_64::rsi);
			getpropa(x86_64::rdx);
			getpropa(x86_64::rcx);
			getpropa(x86_64::r8);
			getpropa(x86_64::r9);*/
		}else if(opcode == 0x2f || opcode == 0x2e || opcode == 0x10e){
			pseen.clear();
			tracepropa_bb(f, b, bobj,decoder, x86_64::rax, firstAddr);
			pseen.clear();
			tracepropa_bb(f, b, bobj,decoder, x86_64::rdx, firstAddr);
		}else{
            if(opcode != 0x15b && opcode != 0x8 && opcode != 0x19 && opcode != 0x15 &&
				opcode != 0x7 && opcode != 0xe && opcode != 0x14 && opcode != 0x11 && opcode != 0x3 &&
                opcode != 0xf && opcode != 0x10 && opcode != 0x18 && opcode != 0x6 && opcode != 0x0 &&
                opcode != 0xc && opcode != 0x2 && opcode != 0xf4 && opcode != 0x17 && opcode != 0x13&&
                opcode != 0x16 && opcode != 0x5 && opcode != 0x12 && opcode != 0x38 
                &&/*opcode != e_push && opcode != e_pop &&*/ opcode != 0x2f/*ret near*/ && opcode != 0x58/*cdq*/ &&
                opcode != 0x89/*cwde*/ && opcode != 0x244/*ud2*/ && opcode != 0x10e/*leave*/ && opcode!= 0x107/*iret*/ &&
                opcode != 0x230/*sti*/ && opcode != 0x32/*prefetchT0*/ && opcode != 0x160/*out*/ && opcode != 0x2e/*ret far*/ 
				){
				if(opcode == 0x2f || opcode == 0x2e || opcode == 0x10e){
					pseen.clear();
					tracepropa_bb(f, b, bobj,decoder, x86_64::rax, firstAddr);
					pseen.clear();
					tracepropa_bb(f, b, bobj,decoder, x86_64::rdx, firstAddr);
					/*getpropa(x86_64::rax);
					getpropa(x86_64::rdx);*/
				}
				//fprintf(insp,"%x,%s, %x\n", firstAddr, instr.format().c_str(), opcode);
				procheck = 0;
			}
        }
		procheck = 0;
    }else if(f->region()->getArch() == Arch_aarch64){
		if(opcode == 0xa46 || opcode == 0xaea || opcode == 0xa14 || opcode == 0xa4c || opcode == 0x920 || opcode == 0xa19 ||
			opcode == 0xa49){
			operand_analysis(f, b, decoder, bobj,instr, firstAddr, procheck, pout, false, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0);
		}
	}
	firstAddr += instr.size();
	}
	return bobj;	
}

struct loopinfo loopornot(Dyninst::ParseAPI::Function *f, dp::Block *b, std::vector<Dyninst::ParseAPI::LoopTreeNode*> tkid){
	vector<dp::Block*> tbb;
    vector<dp::Block*> tempbb;
    vector<dp::Block*> tempe;
    vector<dp::Block*> entries;
    tbb.clear();
    entries.clear();
	tempbb.clear();
	tempe.clear();
	struct loopinfo info;
	info.echo = 0;
	info.lpy = false;
	info.lpb.clear();
	info.lpentry.clear();
	int echo = 1;
    for(Dyninst::ParseAPI::LoopTreeNode* tt: tkid){
		tt->loop->getLoopBasicBlocks(tbb);
        tt->loop->getLoopEntries(entries);
        //std::cout<<"loop"<<echo<<"\n";
        vector<dp::Block*> temp;
        if(echo ==1){
            for(dp::Block *b1 : tbb){
				if(b->start() == b1->start()){
                    info.lpy = true;
					info.echo = echo;
					info.lpb = tbb;
					info.lpentry = entries;
                }
                //std::cout<<"loop"<<echo<<"-"<<std::hex << b1->start() << "\n";
            }   
            /*for(dp::Block *b : entries){
                std::cout<<"loop1"<<echo<<"-"<<b->start() << "\n";
            }*/
        }else{  
            set_difference(tbb.begin(), tbb.end(), tempbb.begin(), tempbb.end(), inserter(temp, temp.begin()));
            set_difference(entries.begin(), entries.end(), tempbb.begin(),tempbb.end(), inserter(tempe, tempe.begin()));
            for(dp::Block *b2 : temp){
				if(b->start() == b2->start()){
					info.lpy = true;
                    info.echo = echo;
                    info.lpb = temp; 
                    info.lpentry = tempe;
                }
				//std::cout <<"loop"<<echo<<"-"<<std::hex<< b2->start() << "\n";
			}
            /*for(dp::Block *b : tempe){
                std::cout<<"loop2"<<echo<<"-"<<b->start() << "\n";
            }*/
        }
		echo++;
		tempbb = tbb;
	}
	return info;
}

std::unordered_set<Dyninst::Address> seenloop;

mkv* traceloop(Dyninst::ParseAPI::Function *f, dp::Block *b, Dyninst::Address entryaddr, int procheck,
Dyninst::InstructionAPI::InstructionDecoder decoder, bool initial, vector<dp::Block*> lb, mht* tab){//need identify which hashtble use
    std::set<MachRegister> tc_reg;
    std::set<MachRegister> tz_reg;
    std::set<MachRegister> ic_reg;
    std::set<MachRegister> iz_reg;
	std::set<MachRegister> lc_reg;
	std::set<MachRegister> lz_reg;
    tc_reg.clear();
    tz_reg.clear();
    ic_reg.clear();
    iz_reg.clear();
	lc_reg.clear();
	lz_reg.clear();
    int tcount = 0;
	int lcount = 0;
	bool islb = false;
	bool srclb = false;
	bool outf = false;
	if(tab == ht3){
		outf = true;
	}
    for(dp::Edge *esrc : b->sources()){
		if (seenloop.count(b->start()) > 0){
			continue;
		}
		seenloop.insert(b->start());
		/*if(std::find(lb.begin(),lb.end(),esrc->src()) != lb.end()){//current loop
            continue;//if the bb is not in this loop, stop.
        }*/
		for(dp::Block* lbb : lb){
			if(esrc->src()->start() == lbb->start()){
				islb = true;
			}
		}
		if(!islb){
			continue;
		}
        if(esrc->src()->start() == entryaddr){//when enter data, careful about the which hashtable should be used
            //std::cout <<"traceloop1-"<< std::hex << esrc->src()->start() << "\n";
            mkv *p = search(tab ,entryaddr);
            if(p == NULL){
                if(tab == ht1){
					p = traceback(f, b, f->entry()->start(), procheck, decoder, initial, true);
				}else if(tab == ht2){
					for(dp::Edge *es : esrc->src()->sources()){
						srclb = false;
						for(dp::Block* bq : lb){
							if(bq->start() == es->src()->start()){
								srclb = true;
							}
						}
						if(!srclb){
							continue;
						}
						mkv* xx = search(ht1, es->src()->start());
						if(xx == NULL){
							xx = traceloop(f, es->src(),entryaddr, procheck, decoder, initial, lb, ht1);
						}
						if(lcount == 0){
							lc_reg = xx->creg;
							lz_reg = xx->zreg;
							lcount++;
						}else{
							tc_reg.clear();
							tz_reg.clear();
							tc_reg = lc_reg;
							tz_reg = lz_reg;
							lc_reg.clear();
							lz_reg.clear();
							std::set_intersection(tc_reg.begin(), tc_reg.end(),
								xx->creg.begin(), xx->creg.end(), inserter(lc_reg, lc_reg.begin()));
							std::set_intersection(tz_reg.begin(), tz_reg.end(),
								xx->zreg.begin(), xx->zreg.end(), inserter(lz_reg, lz_reg.begin()));
							lcount++;
						}

					}
					mkv *bbd = blockanalysis(f, b, procheck, decoder, lc_reg, lz_reg, false);
					p = insert(ht2, b->start(), bbd->creg, bbd->zreg, initial);
					free(bbd);
				}else if(tab == ht3){
					for(dp::Edge *es : esrc->src()->sources()){
                        srclb = false;
						for(dp::Block* bq : lb){ 
                            if(bq->start() == es->src()->start()){
                                srclb = true;
                            }
                        }
                        if(!srclb){
                            continue;
                        }
                        mkv *xx = search(ht2, es->src()->start());
                        if(xx == NULL){
                            xx = traceloop(f, es->src(),entryaddr, procheck, decoder, initial, lb, ht1);
                        }
                        if(lcount == 0){
                            lc_reg = xx->creg; 
                            lz_reg = xx->zreg;
                            lcount++;
                        }else{
                            tc_reg.clear();
                            tz_reg.clear();
                            tc_reg = lc_reg;
                            tz_reg = lz_reg;
                            lc_reg.clear();
                            lz_reg.clear();
                            std::set_intersection(tc_reg.begin(), tc_reg.end(),
                                xx->creg.begin(), xx->creg.end(), inserter(lc_reg, lc_reg.begin()));
                            std::set_intersection(tz_reg.begin(), tz_reg.end(),
                                xx->zreg.begin(), xx->zreg.end(), inserter(lz_reg, lz_reg.begin()));
							lcount++;
						}    

                    }
					mkv *bbd = blockanalysis(f, b, procheck, decoder, lc_reg, lz_reg, false);
                    p = insert(ht3, b->start(), bbd->creg, bbd->zreg, initial);
					free(bbd);
				}
			}
            if(tcount == 0){
                ic_reg = p->creg;
                iz_reg = p->zreg;
                tcount++;
            }else{
                tc_reg.clear();
                tz_reg.clear();
                tc_reg = ic_reg;
                tz_reg = iz_reg;
                ic_reg.clear();
                iz_reg.clear();
                std::set_intersection(tc_reg.begin(), tc_reg.end(),
                    p->creg.begin(), p->creg.end(), inserter(ic_reg, ic_reg.begin()));//common set:tempc_reg and checked_reg
                std::set_intersection(tz_reg.begin(), tz_reg.end(),
                    p->zreg.begin(), p->zreg.end(), inserter(iz_reg, iz_reg.begin()));//common set:tempz_reg and zero_reg
                tcount++;
            }
		}else if(!(esrc->interproc())){
            //std::cout <<"traceloop2-"<< std::hex << esrc->src()->start() << "\n";
            //initial = false;
            mkv *p = search(tab ,esrc->src()->start());
            
			if(p == NULL){
                p = traceloop(f, esrc->src(), entryaddr, procheck, decoder, initial, lb, tab);
			}   
			if(tcount == 0){
                ic_reg = p->creg;
                iz_reg = p->zreg;
                tcount++;
            }else{
                tc_reg.clear();
                tz_reg.clear();
                tc_reg = ic_reg;
                tz_reg = iz_reg;
                ic_reg.clear();
                iz_reg.clear();
                std::set_intersection(tc_reg.begin(), tc_reg.end(),
                    p->creg.begin(), p->creg.end(), inserter(ic_reg, ic_reg.begin()));//common set:tempc_reg and checked_reg
                std::set_intersection(tz_reg.begin(), tz_reg.end(),
                    p->zreg.begin(), p->zreg.end(), inserter(iz_reg, iz_reg.begin()));//common set:tempz_reg and zero_reg
                tcount++;
            }
        }
    }
    mkv *bbd = blockanalysis(f, b, procheck, decoder, ic_reg, iz_reg, outf);
    mkv *q = insert(tab, b->start(), bbd->creg, bbd->zreg, initial);
	free(bbd);
    return q;
}

mkv* loop_output(Dyninst::ParseAPI::Function *f, dp::Block *b, Dyninst::Address loopentry, int procheck,
	Dyninst::InstructionAPI::InstructionDecoder decoder, vector<dp::Block*> lb){
	
	//std::unordered_set<Dyninst::Address> &seelb;
	std::set<MachRegister> tc_reg;
    std::set<MachRegister> tz_reg;
	std::set<MachRegister> ic_reg;
    std::set<MachRegister> iz_reg;
	
	std::unordered_set<Dyninst::Address> seenbb;
	seenbb.clear();
    tc_reg.clear();
    tz_reg.clear();
    ic_reg.clear();
    iz_reg.clear();
    int tcount = 0;
	for(dp::Block *bb : lb){
		if (seenbb.count(bb->start()) > 0)
			continue;
        seenbb.insert(bb->start());
		mkv* y = search(ht0, b->start());
		if(y == NULL){
			if(bb->start() == loopentry){
				mkv* h1 = search(ht1, loopentry);
				if(h1 == NULL){
					traceback(f, bb, f->entry()->start(), procheck, decoder, true, true);
				}
				//traceloop(f,bb,loopentry,procheck, decoder, true, lb, ht[1]);
			}else{
				for (dp::Edge *e : bb->sources()){
					if (seenbb.count(e->src()->start()) > 0)
						continue;
					mkv* q = search(ht1, e->src()->start());
					if(q == NULL){
						traceloop(f,bb,loopentry,procheck, decoder, true, lb, ht1);
					}
				}
			}
		}
	}
	//seelb.clear();
	
	for(dp::Block *bb : lb){
		mkv* h1 = search(ht1, bb->start());
		if(h1 == NULL){
			h1 = traceloop(f,bb,loopentry,procheck, decoder, true, lb, ht1);
		}
		if(bb->start()==loopentry){
			for(dp::Edge *e : bb->sources()){
				if(std::find(lb.begin(), lb.end(),e->src()) != lb.end()){//current loop
					continue;
				}
				mkv* he = search(ht1, e->src()->start());
				//std::cout<< bb->start()<<"\n";
	 			if(he == NULL){
					he = traceloop(f,bb,loopentry,procheck, decoder, true, lb, ht1);
				}
				mkv *bbd = blockanalysis(f, bb, procheck, decoder, he->creg, he->zreg, false);
				std::set_intersection(bbd->creg.begin(), bbd->creg.end(),
                    h1->creg.begin(), h1->creg.end(), inserter(ic_reg, ic_reg.begin()));//common set:tempc_reg and checked_reg
				std::set_intersection(bbd->zreg.begin(), bbd->zreg.end(),
                    h1->zreg.begin(), h1->zreg.end(), inserter(iz_reg, iz_reg.begin()));
				free(bbd);
			}
			insert(ht2, b->start(), ic_reg, iz_reg, true);
		}else{
			mkv* q = search(ht2, bb->start());
			if(q == NULL){
				traceloop(f,bb,loopentry,procheck, decoder, true, lb, ht2);
			}
		}
	}
	
	//seelb.clear();
	for(dp::Block *bb : lb){ 
        mkv* h2 = search(ht2, bb->start());
		if(h2 == NULL){
			h2 = traceloop(f,bb,loopentry,procheck, decoder, true, lb, ht2);
		}
        if(bb->start()==loopentry){
            for(dp::Edge *e : bb->sources()){
                if(std::find(lb.begin(), lb.end(),e->src()) != lb.end()){//current loop
                    continue;
                }    
                mkv* he = search(ht2, e->src()->start());
                //std::cout<< bb->start()<<"\n";
                if(he == NULL){
					he = traceloop(f,bb,loopentry,procheck, decoder, true, lb, ht2);
                }
                mkv* bbd = blockanalysis(f, bb, procheck, decoder, he->creg, he->zreg, true);
                std::set_intersection(bbd->creg.begin(), bbd->creg.end(),
                    h2->creg.begin(), h2->creg.end(), inserter(ic_reg, ic_reg.begin()));//common set:tempc_reg and checked_reg
                std::set_intersection(bbd->zreg.begin(), bbd->zreg.end(),
                    h2->zreg.begin(), h2->zreg.end(), inserter(iz_reg, iz_reg.begin()));
				free(bbd);
            }
            insert(ht3, b->start(), ic_reg, iz_reg, true);
        }else{
            mkv* q = search(ht3, bb->start());
            if(q == NULL){
				traceloop(f,bb,loopentry,procheck, decoder, true, lb, ht3);
            }    
        }    
    }
	mkv* t1 = search(ht2, b->start());
	mkv* t2 = search(ht3, b->start());
	set_difference(t1->creg.begin(), t1->creg.end(), t2->creg.begin(), t2->creg.end(), inserter(tc_reg, tc_reg.begin()));
	set_difference(t1->zreg.begin(), t1->zreg.end(), t2->zreg.begin(), t2->zreg.end(), inserter(tz_reg, tz_reg.begin()));
	if(tc_reg.empty() && tz_reg.empty()){
		insert(ht0, b->start(), t1->creg, t1->zreg, false);
	}else{
		//insert(ht0, b->start(), t1->creg, t1->zreg, false);
		//printf("unfin loop, no result");
		//exit(-1);
	}

}

std::unordered_set<Dyninst::Address> seentraceback;

mkv* traceback(Dyninst::ParseAPI::Function *f, dp::Block *b, Dyninst::Address entryaddr, int procheck,
    Dyninst::InstructionAPI::InstructionDecoder decoder, bool initial, bool firstrace){
    std::set<MachRegister> tc_reg;
    std::set<MachRegister> tz_reg;
	std::set<MachRegister> ic_reg;
    std::set<MachRegister> iz_reg;
    std::set<MachRegister> checked_reg;
	std::set<MachRegister> zero_reg;
	tc_reg.clear();
    tz_reg.clear();
	ic_reg.clear();
	iz_reg.clear();
	checked_reg.clear();
	zero_reg.clear();
    int tcount = 0;
	int echo = 0;
	bool bblong = false;
	vector<dp::Block*> tbb;
	vector<dp::Block*> tempee;
    vector<dp::Block*> tempbb;
    vector<dp::Block*> entries;
	std::vector<Dyninst::ParseAPI::LoopTreeNode*> tkid;
	tkid = f->getLoopTree()->children;
    tbb.clear();
	mkv* hasobj = search(ht0, b->start());
	if(hasobj == NULL){
	for(dp::Edge *esrc : b->sources()){
		struct loopinfo qq = loopornot(f, esrc->src(), tkid);
		if (seentraceback.count(b->start()) > 0){
             continue;
        }
        seentraceback.insert(b->start());
		if(qq.lpy && (!(esrc->interproc()))){//if we trace back the loop entry block, at the first time traceback, we should ignore the source block belongs to this loop.
			if (seentraceback.count(b->start()) > 0){
				continue;
			}
			seentraceback.insert(b->start());
			if(firstrace){
				firstrace = false;
				continue;
			}
			mkv *s = search(ht0,esrc->src()->start());
			if(s == NULL){
				for(dp::Block* le : qq.lpentry){
					s = loop_output(f, b, le->start(), procheck, decoder, qq.lpb);
					if(tcount == 0){
						ic_reg = s->creg;
						iz_reg = s->zreg;
						tcount++;
					}else{
						tc_reg.clear();
						tz_reg.clear();
						tc_reg = ic_reg;
						tz_reg = iz_reg;
						ic_reg.clear();
						iz_reg.clear();
						std::set_intersection(tc_reg.begin(), tc_reg.end(),
							s->creg.begin(), s->creg.end(), inserter(ic_reg, ic_reg.begin()));//common set:tempc_reg and checked_reg
						std::set_intersection(tz_reg.begin(), tz_reg.end(),
							s->zreg.begin(), s->zreg.end(), inserter(iz_reg, iz_reg.begin()));//common set:tempz_reg and zero_reg
						tcount++;
					}
				}
			}else{
				if(tcount == 0){
					ic_reg = s->creg;
                    iz_reg = s->zreg;
                    tcount++;
                }else{
                    tc_reg.clear();
                    tz_reg.clear();
                    tc_reg = ic_reg;
                    tz_reg = iz_reg;
                    ic_reg.clear();
                    iz_reg.clear();
                    std::set_intersection(tc_reg.begin(), tc_reg.end(),
                        s->creg.begin(), s->creg.end(), inserter(ic_reg, ic_reg.begin()));//common set:tempc_reg and checked_reg
                    std::set_intersection(tz_reg.begin(), tz_reg.end(),
                        s->zreg.begin(), s->zreg.end(), inserter(iz_reg, iz_reg.begin()));//common set:tempz_reg and zero_reg
                    tcount++;
                }
			}
			continue;
		}
		if(esrc->src()->start() == entryaddr){
            //std::cout <<"traceback1-"<< std::hex << esrc->src()->start() << "\n";
            initial = false;
			mkv *p = search(ht0,entryaddr);
            if(p == NULL){
                checked_reg.clear();
                zero_reg.clear();
                mkv *ss = blockanalysis(f,esrc->src(),procheck, decoder, checked_reg, zero_reg, false);
                p = insert(ht0, esrc->src()->start(), ss->creg, ss->zreg, initial);
				free(ss);
			}
			ic_reg = p->creg;
            iz_reg = p->zreg;
            tcount++;
        }else if(!(esrc->interproc())){
            //std::cout <<"traceback2-"<< std::hex << esrc->src()->start() << "\n";
			initial = false;
            mkv *p = search(ht0,esrc->src()->start());
            if(p == NULL){
                p = traceback(f, esrc->src(), entryaddr, procheck, decoder, initial, false);
			}
			if(tcount == 0){
                ic_reg = p->creg;
                iz_reg = p->zreg;
                tcount++;
            }else{
				tc_reg.clear();
                tz_reg.clear();
                tc_reg = ic_reg;
                tz_reg = iz_reg;
                ic_reg.clear();
                iz_reg.clear();
                std::set_intersection(tc_reg.begin(), tc_reg.end(),
                    p->creg.begin(), p->creg.end(), inserter(ic_reg, ic_reg.begin()));//common set:tempc_reg and checked_reg
                std::set_intersection(tz_reg.begin(), tz_reg.end(),
                    p->zreg.begin(), p->zreg.end(), inserter(iz_reg, iz_reg.begin()));//common set:tempz_reg and zero_reg
				tcount++;
            }
        }
    }
	mkv *q;
	if(initial){
		q = blockanalysis(f, b, procheck, decoder, ic_reg, iz_reg, false);
		hasobj = insert(ht1, b->start(), checked_reg, zero_reg, initial);
	}else{
		q = blockanalysis(f, b, procheck, decoder, ic_reg, iz_reg, true);
		hasobj = insert(ht0, b->start(), checked_reg, zero_reg, initial);
	}
	free(q);
	}
	return hasobj;
}

int main(int argc, char* argv[]) {
	if (argc < 2 || argc > 3) {
		std::cerr << "Usage: " << argv[0] << " executable\n";
		return -1;
	}
	//funcname = argv[2];
	instru_count_app = 0;
	detect_opt_app = 0;
	propa_opt_app = 0;
	totalcount_app = 0;
	best_detectopt = 0;
	best_propaopt = 0;
	best_instruopt = 0;
	best_detectfunc = NULL;
	best_propaofunc = NULL;
	best_instrufunc = NULL;
	std::cout << "main"<< '\n';
	//printf("%s\p", funcname);
	auto *sts = new dp::SymtabCodeSource(argv[1]);
	auto *co = new dp::CodeObject(sts);
	Dyninst::InstructionAPI::Instruction instr;
	fp = fopen("analysis.txt", "w");
	FILE *inf = fopen("info.txt", "w");
	// Parse the binary
	co->parse();

	std::cout << "digraph G {" << '\n';
	std::cout << "digraph G {" << '\n';
	// Print the control flow graph
	dp::CodeObject::funclist all = co->funcs();
	// Remove compiler-generated and system functions
	{
		auto ignore = [&all](dp::Function const *f) {
			auto const &name = f->name();
			bool const starts_with_underscore = name[0] == '_';
			bool const ends_with_underscore = name[name.length() - 1] == '_';
			bool const is_dummy = name == "frame_dummy";
			bool const is_clones = name.find("tm_clones") != std::string::npos;
			if(f->region()->getArch() == Arch_x86_64){
				savereg = {x86_64::rbp,x86_64::rsp,x86_64::rbx,x86_64::r12,x86_64::r13,x86_64::r14, x86_64::r15};
			}else if(f->region()->getArch() == Arch_aarch64){
				savereg = {aarch64::sp,aarch64::x19};
			}
			return starts_with_underscore || ends_with_underscore || is_dummy ||
					is_clones;
		};
		// 'funclist' is a std::set which has only const iterators
		auto i = all.begin();
		while (i != all.end()) {
			if (ignore(*i)) {
				i = all.erase(i);
			}
			else{
				++i;
			}
		}
	}
	//auto const *f : all;

	std::unordered_set<Dyninst::Address> seen;
	//std::unordered_set<Dyninst::Address> seen2;
	int cluster_index = 0;
	for (auto *f : all) {
		ht0 = Init(0xffff);
		ht1 = Init(0xffff);
		ht2 = Init(0xffff);
		ht3 = Init(0xffff);
		bool initial = false;
		int procheck;
		reInit(rht);
		seenloop.clear();
		seentraceback.clear();
		curr_point_f = 0;
		prev_point_f = 0;
		detect_opt_f = 0;
		propa_opt_f = 0;
		instru_count_f = 0;
		totalcount_f = 0;
		Dyninst::InstructionAPI::InstructionDecoder decoder(f->isrc()->
											getPtrToInstruction(f->addr()),
        Dyninst::InstructionAPI::InstructionDecoder::maxInstructionLength,
        f->region()->getArch());
		// Make a cluster for nodes of this function
		std::cout << "\t subgraph cluster_" << cluster_index << " { \n\t\t label=\""
              << f->name() << "\"; \n\t\t color=blue;" << '\n';

		std::cout << "\t\t\"" << std::hex << f->addr() << std::dec
              << "\" [shape=box";

		if (f->retstatus() == dp::NORETURN)
			std::cout << ",color=red";

		std::cout << "]" << '\n';

		// Label functions by name
		std::cout << "\t\t\"" << std::hex << f->addr() << std::dec
              << "\" [label = \"" << f->name() << "\\n"
              << std::hex << f->addr() << std::dec << "\"];" << '\n';

		std::stringstream edgeoutput;
		vector<dp::Loop*> loops;
		Dyninst::ParseAPI::LoopTreeNode* lptrees;
		std::vector<Dyninst::ParseAPI::LoopTreeNode*> tkid;
		tkid.clear();
		loops.clear();
		f->getLoops(loops);
		lptrees = f->getLoopTree();	
		tkid = lptrees->children;
		printf("loop num:0x%lx\n", tkid.size());

		for (dp::Block *b : f->blocks()) {
			// Don't revisit blocks in shared code
			if (seen.count(b->start()) > 0)
				continue;
			int echo = 1;
			bool isloop = false;
			Dyninst::Address lastAddr = b->end();
			Dyninst::Address firstAddr = b->start();
			
			vector<dp::Block*> tbb;
			vector<dp::Block*> tempbb;
			vector<dp::Block*> tempe;
			vector<dp::Block*> entries;
			vector<dp::Block*> te;
			vector<dp::Block*> temploo;
			tbb.clear();
			entries.clear();
			tempbb.clear();
			tempe.clear();
			temploo.clear();
			te.clear();
			for(Dyninst::ParseAPI::LoopTreeNode* tt: tkid){
				tt->loop->getLoopBasicBlocks(tbb);
				tt->loop->getLoopEntries(entries);
				tempbb.clear();
				//std::cout<<"loop"<<echo<<"\n";
				if(echo ==1){
					for(dp::Block *b1 : tbb){
						if(b->start() == b1->start()){
							isloop = true;
							tempbb = tbb;
							tempe = entries;
							break;
						}
						//std::cout<<"loop"<<echo<<"-"<<std::hex << b1->start() << "\n";
						
					}
				}else{
					set_difference(tbb.begin(), tbb.end(), temploo.begin(), temploo.end(), inserter(tempbb, tempbb.begin()));
					set_difference(entries.begin(), entries.end(), te.begin(),te.end(), inserter(tempe, tempe.begin()));
					for(dp::Block *b2 : tempbb){
						if(b->start() == b2->start()){
                        	isloop = true;	
							break;
                    	}
						//std::cout<<"loop"<<echo<<"-"<<std::hex << b2->start() << "\n";
					}
				}
				if(isloop){
					break;
				}
				temploo = tbb;
				echo++;
			}
			
			if(!isloop){ 
				mkv *p = search(ht0, b->start());
				if(p == NULL){
					traceback(f, b, f->entry()->start(), 1, decoder, true, true);
				}
			}else{
				vector<dp::Block*> lbb;
				vector<dp::Block*> le;
				lbb.clear();
				le.clear();
				//cout<<"loop block: "<<std::hex <<b->start()<<"\n";
				if(echo <= 2){ 
					lbb = tbb;
					le = entries;
				}else{ 
					lbb = tempbb;
					le = tempe;
				}
				initial = true;
				for(dp::Block *lb : le){
					//cout<<"loop entry: "<< std::hex<<b->start()<<"\n";
					mkv *p = search(ht0, b->start());
					if(p == NULL){
						p = traceback(f, b, f->entry()->start(), procheck, decoder, initial, true);//traceback need to ignore the block in loop
					}
					loop_output(f, b, lb->start(), procheck, decoder,lbb); 
				}
				/*for(dp::Block *lentry : entries){
					cout<<"--------------"<<"entry: "<< std::hex<<lentry->start()<<"\n";
				}
				for(dp::Block *lbs : tempbb){
					cout<<"--------------"<<"loop: "<< std::hex<<lbs->start()<<"\n";
				}*/
			}
			getinstru(f, b, decoder);

			while(firstAddr < lastAddr){
				instr = decoder.decode((unsigned char *)f->isrc()->getPtrToInstruction(firstAddr));
				cout << "\n" << hex << firstAddr;
				cout << ": \"" << instr.format() << "\"";
				firstAddr += instr.size();
			}
			seen.insert(b->start());

			std::cout << "\t\t\"" << std::hex << b->start() << std::dec << "\";"
                << '\n';

			for (dp::Edge *e : b->targets()) {
				if (!e)
					continue;
				std::string s;
			if (e->type() == dp::CALL)
				s = " [color=blue]";
			else if (e->type() == dp::RET)
				s = " [color=green]";

			// Store the edges somewhere to be printed outside of the cluster
			edgeoutput << "\t\"" << std::hex << e->src()->start() << "\" -> \""
                   << e->trg()->start() << "\"" << s << '\n';
			}
		}
		double detopt = (double)detect_opt_f/(double)totalcount_f*100;
		double proopt = (double)propa_opt_f/(double)totalcount_f*100;
		double instropt = (double)(totalcount_f-instru_count_f)/(double)totalcount_f*100;
		if(detopt > best_detectopt && detopt != 0){
			best_detectopt = detopt;
			best_detectfunc = (char*)f->name().c_str();
			best_detectfaddr = f->addr();
		}
		if(proopt > best_propaopt && proopt != 0){
			best_propaopt = proopt;
			best_propaofunc = (char*)f->name().c_str();
			best_propafaddr = f->addr();
		}
		if(instropt > best_instruopt && instru_count_f != 0){
			best_instruopt = instropt;
			best_instrufunc = (char*)f->name().c_str();
			best_instrufaddr = f->addr();
		}
		
		fprintf(inf,"detect opt:0x%lx, propa opt: 0x%lx, instru opt:0x%lx, 0x%lx, %s\n", detect_opt_f, propa_opt_f, instru_count_f, totalcount_f, f->name().c_str());
		fprintf(inf,"detect opt: %f%, propa opt: %f%, instru opt: %f%\n", detopt, proopt, instropt);

		// End cluster
		std::cout << "\t}" << '\n';

		// Print edges
		std::cout << edgeoutput.str() << '\n';
		destroy(ht0);
		destroy(ht1);
		destroy(ht2);
		destroy(ht3);
		redestory(rht);
	}
	fprintf(inf,"0x%lx, 0x%lx, 0x%lx, 0x%lx\n", detect_opt_app, propa_opt_app, instru_count_app, totalcount_app);
	fprintf(inf, "BEST DETECT OPT FUNC: %s, 0x%lx, %f%\n", best_detectfunc, best_detectfaddr ,best_detectopt);
	fprintf(inf, "BEST PROPA OPT FUNC: %s, 0x%lx, %f%\n", best_propaofunc, best_propafaddr, best_propaopt);
	fprintf(inf, "BEST INSTRU OPT FUNC: %s, 0x%lx, %f%\n", best_instrufunc, best_instrufaddr,best_instruopt);
	std::cout << "}" << '\n';
	fclose(fp);
	fclose(inf);
}
