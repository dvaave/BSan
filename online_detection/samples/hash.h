#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
extern FILE *dect;
extern int hhh;

//#define SIZE 0xffffff

struct DataItem {
   unsigned long address;   
   unsigned long key;
   unsigned long size;
   bool initial;
   int vaild;
};

struct DataItem *hashArray; 
struct DataItem dummyItem = {0,0,0,0,0};
//struct DataItem erroritem = {-1,-1,-1};
struct DataItem* item;
unsigned long h_size = 0xffffff;

unsigned long hashCode(unsigned long key) {
   return (key - 0x8000000000000000);
}

struct DataItem* hinitial(unsigned long h_size){

    hashArray = (struct DataItem*)malloc(h_size*sizeof(struct DataItem));
    return hashArray;
}

struct DataItem* hgrowsize(struct DataItem *ptr, unsigned long newsize){

   hashArray = (struct DataItem *)realloc(ptr,newsize*sizeof(struct DataItem));
	h_size = newsize;
   return hashArray;
}

struct DataItem hsearch(unsigned long key) {
   //get the hash 
   unsigned long hashIndex = hashCode(key);
   if(hashIndex > h_size){
      return dummyItem;
   }  
	
   //move in array until an empty 
   if(hashArray[hashIndex].key == key ) {
		return hashArray[hashIndex]; 
   }        
   else return dummyItem;        
}

void hinsert(unsigned long key,unsigned long address, unsigned long size, int valid, bool init) {

   //struct DataItem *item = (struct DataItem*) malloc(sizeof(struct DataItem));
	unsigned long hk = hashCode(key);
   if((double)(hk/h_size)>0.75){
		hgrowsize(hashArray, 2*h_size);
	}

	if(hk < h_size){
		hashArray[hk].address = address;  
		hashArray[hk].key = key;
		hashArray[hk].size = size;
      hashArray[hk].initial = init;
      hashArray[hk].vaild = 1;
	}
}

bool hfree(unsigned long key) {
   //get the hash 
   unsigned long hk = hashCode(key);
	if(hashArray[hk].key == key) {
      if(hashArray[hk].vaild == 1){
         hashArray[hk].vaild = 0;
         return true;
      }else{
         //fprintf(dect,"double free detected in id 0x%lx\n", key);
         if(hhh == 0){
            hhh = 1;
            //fprintf(dect,"PPPP\n");
         }
         return false;
      }
   }
   return true;        
}

void meminit(unsigned long key){
   
}

/*void destroy_hash(struct DataItem hashArray){
	free(hashArray);
}*/

void hdisplay() {
   unsigned long i = 0;	
   for(i = 0; i<h_size; i++) {
      //if(hashArray[i] != NULL)
         //printf("(%ld,%012lx, %ld)\n",hashArray[i].key,hashArray[i].address, hashArray[i].size);
      //else
         //printf("  ");
   }
   printf("\n");
}
