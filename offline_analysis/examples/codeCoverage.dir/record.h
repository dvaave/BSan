#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
#include <assert.h>


#define m 0xffffff
using namespace Dyninst;
typedef struct reDataType
{
	Dyninst::InstructionAPI::Instruction ins;
	Dyninst::Address startaddr;
	MachRegister regsrc;
	bool numsrc;
	MachRegister regdst;
	int memaccess;//0 is no access, 1 is src read, 2 is dst read, 3 is dst write
	bool psrc;
	int detect;
	int propa;
	
}reDataType;

typedef struct reNode
{   
	reDataType redata;
	struct reNode* renext;
}reNode;

typedef struct 
{
    
	reNode* renext;
}reHashTable[m];

void reInit(reHashTable ht)
{
    
	assert(ht != NULL);
	if (ht == NULL)
	{
		return;
	}
	for (int i = 0; i < m; i++)
	{
		ht[i].renext = NULL;
	}
}

MachRegister ureg(MachRegister reg){
	switch((unsigned long)reg){
        case(0x18010000):case(0x18010f00):
            reg = x86_64::rax;
            break;
        case(0x18010001):case(0x18010f01):
            reg = x86_64::rcx;
            break;
        case(0x18010002):case(0x18010f02):
            reg = x86_64::rdx;
            break;
        case(0x18010003):case(0x18010f03):
            reg = x86_64::rbx;
            break;
        case(0x18010004):case(0x18010f04):
            reg = x86_64::rsp;
            break;
        case(0x18010005):case(0x18010f05):
            reg = x86_64::rbp;
            break;
        case(0x18010006):case(0x18010f06):
            reg = x86_64::rsi;
            break;
        case(0x18010007):case(0x18010f07):
            reg = x86_64::rdi;
            break;
        case(0x18010008):case(0x18010f08):
            reg = x86_64::r8;
            break;
        case(0x18010009):case(0x18010f09):
            reg = x86_64::r9;
            break;
        case(0x1801000a):case(0x18010f0a):
            reg = x86_64::r10;
            break;
        case(0x1801000b):case(0x18010f0b):
            reg = x86_64::r11;
            break;
        case(0x1801000c):case(0x18010f0c):
            reg = x86_64::r12;
            break;
        case(0x1801000d):case(0x18010f0d):
            reg = x86_64::r13;
            break;
        case(0x1801000e):case(0x18010f0e):
            reg = x86_64::r14;
            break;
        case(0x1801000f):case(0x18010f0f):
            reg = x86_64::r15;
            break;
		case(0x48010000):case(0x48010f00):
			reg = aarch64::x0;
			break;
		case(0x48010001):case(0x48010f01):
			reg = aarch64::x1;
			break;
		case(0x48010002):case(0x48010f02):
            reg = aarch64::x2;
            break;
		case(0x48010003):case(0x48010f03):
            reg = aarch64::x3;
            break;
		case(0x48010004):case(0x48010f04):
            reg = aarch64::x4;
            break;
		case(0x48010005):case(0x48010f05):
            reg = aarch64::x5;
            break;
		case(0x48010006):case(0x48010f06):
            reg = aarch64::x6;
            break;
		case(0x48010007):case(0x48010f07):
            reg = aarch64::x7;
            break;
		case(0x48010008):case(0x48010f08):
            reg = aarch64::x8;
            break;
		case(0x48010009):case(0x48010f09):
            reg = aarch64::x9;
            break;
		case(0x4801000a):case(0x48010f0a):
            reg = aarch64::x10;
            break;
		case(0x4801000b):case(0x48010f0b):
            reg = aarch64::x11;
            break;
		case(0x4801000c):case(0x48010f0c):
            reg = aarch64::x12;
            break;
		case(0x4801000d):case(0x48010f0d):
            reg = aarch64::x13;
            break;
		case(0x4801000e):case(0x48010f0e):
            reg = aarch64::x14;
            break;
		case(0x4801000f):case(0x48010f0f):
            reg = aarch64::x15;
            break;
		case(0x48010010):case(0x48010f10):
            reg = aarch64::x16;
            break;
		case(0x48010011):case(0x48010f11):
            reg = aarch64::x17;
            break;
		case(0x48010012):case(0x48010f12):
            reg = aarch64::x18;
            break;
		case(0x48010013):case(0x48010f13):
            reg = aarch64::x19;
            break;
		case(0x48010014):case(0x48010f14):
            reg = aarch64::x20;
            break;
		case(0x48010015):case(0x48010f15):
            reg = aarch64::x21;
            break;
		case(0x48010016):case(0x48010f16):
            reg = aarch64::x22;
            break;
		case(0x48010017):case(0x48010f17):
            reg = aarch64::x23;
            break;
		case(0x48010018):case(0x48010f18):
            reg = aarch64::x24;
            break;
		case(0x48010019):case(0x48010f19):
            reg = aarch64::x25;
            break;
		case(0x4801001a):case(0x48010f1a):
            reg = aarch64::x26;
            break;
		case(0x4801001b):case(0x48010f1b):
            reg = aarch64::x27;
            break;
		case(0x4801001c):case(0x48010f1c):
            reg = aarch64::x28;
            break;
		case(0x4801001d):case(0x48010f1d):
            reg = aarch64::x29;
            break;
		case(0x4801001e):case(0x48010f1e):
            reg = aarch64::x30;
            break;
		case(0x4801001f):case(0x48010f1f):
            reg = aarch64::sp;
            break;
		return reg;
    }
}

unsigned long int reH(Dyninst::Address key)
{
	return key % m;
}

reNode* research(const reHashTable ht, Dyninst::Address key)
{
    	
	unsigned long hi = reH(key);
	for (reNode* p = ht[hi].renext; p != NULL; p = p->renext)
	{
		if (p->redata.startaddr == key)
			return p;
	}
	return NULL;
}

reNode* getlastmod(const reHashTable ht, Dyninst::Address key, MachRegister reg){
	unsigned long hi = reH(key);
    reNode *temp = research(ht, key);
    if (temp != NULL)
    {   
		reg = ureg(reg);
		if(temp->redata.regdst == reg){
			if(temp->redata.memaccess == 1){
				return temp;
			}else if(temp->redata.memaccess == 0){
				return temp;
			}
		}
		return NULL;
	}
	return NULL;
}

reNode* getuse(const reHashTable ht, Dyninst::Address key, MachRegister reg){
    unsigned long hi = reH(key);
    reNode *temp = research(ht, key);
    if (temp != NULL)
    {   
        reg = ureg(reg);
        if(temp->redata.regsrc == reg){
            if(temp->redata.memaccess == 1){ 
                return temp;
            }else if(temp->redata.memaccess == 0){ 
                return temp;
            }else if(temp->redata.memaccess == 3){
				return temp;
			}   
        }
		if(temp->redata.regdst == reg && (temp->redata.memaccess == 2 || temp->redata.memaccess == 3)){
			return temp;
		}   
        return NULL;
    }   
    return NULL;
}

reNode* reinsertde(reHashTable ht, Dyninst::Address key, int detect)
{
    
	unsigned long hi = reH(key);
	reNode *temp = research(ht, key);
	if (temp == NULL)
	{
		//temp->data.memid = id;
		//return temp;
	
		reNode* p = (reNode*)calloc(1, sizeof(reNode));
		assert(p != NULL);
		p->redata.startaddr = key;
		p->redata.detect = detect;
		p->redata.propa = 0;
		p->renext = ht[hi].renext;
		ht[hi].renext = p;
		return p;
	}else{
		temp->redata.detect = detect;
		return temp;
	}
}

reNode* reinsertpa(reHashTable ht, Dyninst::Address key, int propa)
{
        
    unsigned long hi = reH(key);
    reNode *temp = research(ht, key);
    if (temp == NULL)
    {   
        //temp->data.memid = id;
        //return temp;
       
		reNode* p = (reNode*)calloc(1, sizeof(reNode));
		assert(p != NULL);
		p->redata.startaddr = key;
		p->redata.detect = 0;
		p->redata.propa = propa;
		p->renext = ht[hi].renext;
		ht[hi].renext = p;
		return p;
	}else{
		temp->redata.propa = propa;
        return temp;
	}
}

reNode* reinsertsrc(reHashTable ht, Dyninst::Address key, MachRegister sreg)
{
            
    unsigned long hi = reH(key);
    reNode *temp = research(ht, key);
    sreg = ureg(sreg); 
	if (temp == NULL)
    {   
        //temp->data.memid = id;
        //return temp;
        //sreg = ureg(sreg);   
		reNode* p = (reNode*)calloc(1, sizeof(reNode));
		assert(p != NULL);
		p->redata.startaddr = key;
		p->redata.regsrc = sreg;
		p->renext = ht[hi].renext;
		ht[hi].renext = p;
		return p;
    }else{
		temp->redata.regsrc = sreg;
        return temp;
	}   
}

reNode* reinsertdst(reHashTable ht, Dyninst::Address key, MachRegister dreg)
{

    unsigned long hi = reH(key);
    reNode *temp = research(ht, key);
    dreg = ureg(dreg);
	if (temp == NULL)
    {
        //temp->data.memid = id;
        //return temp;
		//dreg = ureg(dreg);
        reNode* p = (reNode*)calloc(1, sizeof(reNode));
        assert(p != NULL);
        p->redata.startaddr = key;
        p->redata.regdst = dreg;
        p->renext = ht[hi].renext;
        ht[hi].renext = p;
        return p;
    }else{
        temp->redata.regdst = dreg;
        return temp;
    }
}

/*reNode* reinsertdst(reHashTable ht, Dyninst::Address key, bool memacc)
{

    unsigned long hi = reH(key);
    reNode *temp = research(ht, key);
    if (temp == NULL)
    {
        //temp->data.memid = id;
        //return temp;

        reNode* p = (reNode*)calloc(1, sizeof(reNode));
        assert(p != NULL);
        p->redata.startaddr = key;
        p->redata.memaccess = memacc;
        p->renext = ht[hi].renext;
        ht[hi].renext = p;
        return p;
    }else{
        temp->redata.memaccess = memacc;
        return temp;
    }
}*/

reNode* reinsertmema(reHashTable ht, Dyninst::Address key, int memacc)
{

    unsigned long hi = reH(key);
    reNode *temp = research(ht, key);
    if (temp == NULL)
    {
        //temp->data.memid = id;
        //return temp;

        reNode* p = (reNode*)calloc(1, sizeof(reNode));
        assert(p != NULL);
        p->redata.startaddr = key;
        p->redata.memaccess = memacc;
        p->renext = ht[hi].renext;
        ht[hi].renext = p;
        return p;
    }else{
        temp->redata.memaccess = memacc;
        return temp;
    }
}

reNode* reinsertpsrc(reHashTable ht, Dyninst::Address key, bool psrc)
{

    unsigned long hi = reH(key);
    reNode *temp = research(ht, key);
    if (temp == NULL)
    {
        //temp->data.memid = id;
        //return temp;

        reNode* p = (reNode*)calloc(1, sizeof(reNode));
        assert(p != NULL);
        p->redata.startaddr = key;
        p->redata.psrc = psrc;
        p->renext = ht[hi].renext;
        ht[hi].renext = p;
        return p;
    }else{
        temp->redata.psrc = psrc;
        return temp;
    }
}

reNode* reinsertnumsrc(reHashTable ht, Dyninst::Address key, bool numsrc)
{

    unsigned long hi = reH(key);
    reNode *temp = research(ht, key);
    if (temp == NULL)
    {   
        //temp->data.memid = id;
        //return temp;

        reNode* p = (reNode*)calloc(1, sizeof(reNode));
        assert(p != NULL);
        p->redata.startaddr = key;
        p->redata.numsrc = numsrc;
        p->renext = ht[hi].renext;
        ht[hi].renext = p;
        return p;
    }else{
        temp->redata.numsrc = numsrc;
        return temp;
    }   
}


/*void remove(Node *data){
	if (data != NULL)
	{
		//data->data_idmem.memid = 0;
	}
}*/

void reShow(FILE *fp, reHashTable ht)
{
    
	for (int i = 0; i < m; i++)
	{
    
		//printf("hash%d: ", i);
		for (reNode* p = ht[i].renext; p != NULL; p = p->renext)
		{
			fprintf(fp, "0x%x %x %x %x %d\n", p->redata.startaddr, p->redata.detect, p->redata.propa, p->redata.memaccess, p->redata.psrc);
			//fprintf(fp, "sadas\n");
		}
	}
}

void redestory(reHashTable ht) 
{
        
    for (int i = 0; i < m; i++)
    {   
        
        //printf("hash%d: ", i); 
        for (reNode* p = ht[i].renext; p != NULL; p = p->renext)
        {   
			free(p);
            //printf("0x%lx  ", p->data_idmem.key);
            //printf("0x%lx  ", p->data_idmem.memid);
        }   
        //printf("\n");
    }   
}

/*
int main()
{    
	HashTable ht;
	InitHash(ht);
	unsigned long arr[16] = {
     13,5,7,1,2,9,28,25,6,11,10,15,17,23,34,19 };
	for (int i = 0; i < sizeof(arr) / sizeof(arr[0]); i++)
	{
    
		Insert(ht, arr[i]);
	}
	Show(ht);
	return 0;
}*/
