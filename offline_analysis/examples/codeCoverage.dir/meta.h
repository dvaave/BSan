#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>
#include <assert.h>

#define LOAD_FACTOR_THRESHOLD 0.7
#define GROWTH_FACTOR 2
FILE *ch;
typedef struct mkv {
    Dyninst::Address startaddr;
	std::set<Dyninst::MachRegister> creg;
	std::set<Dyninst::MachRegister> zreg;
	bool initial;
	struct mkv* next;
} mkv;

typedef struct {
    unsigned long size;
    unsigned long count;
    mkv** table;
} mht;

unsigned long H(Dyninst::Address key, unsigned long table_size) {
    // Perform a simple modulo operation for hashing
    return key % table_size;
}

mht* Init(unsigned long size) {
    mht* hashtable = (mht*)malloc(sizeof(mht));
    hashtable->size = size;
    hashtable->count = 0;
    hashtable->table = (mkv**)malloc(size * sizeof(mkv*));
    for (unsigned long i = 0; i < size; i++) {
        hashtable->table[i] = NULL;
    }
    return hashtable;
}

void resize(mht* hashtable) {
    unsigned long old_size = hashtable->size;
    unsigned long new_size = old_size * GROWTH_FACTOR;
    mkv** new_table = (mkv**)calloc(new_size, sizeof(mkv*));

    // Rehash all existing key-value pairs into the new table
    for (unsigned long i = 0; i < old_size; i++) {
        mkv* curr = hashtable->table[i];
        while (curr != NULL) {
            mkv* next = curr->next;
            unsigned long slot = H(curr->startaddr, new_size);
            curr->next = new_table[slot];
            new_table[slot] = curr;
            curr = next;
        }
    }

    // Free the old table and update hashtable properties
    free(hashtable->table);
    hashtable->table = new_table;
    hashtable->size = new_size;
}

mkv* search(mht* hashtable, unsigned long key) {
    unsigned long slot = H(key, hashtable->size);
    mkv* curr = hashtable->table[slot];
    while (curr != NULL) {
        if (curr->startaddr == key) {
            return curr;
        }
        curr = curr->next;
    }
    return NULL;  // startaddr not found
}

mkv* insert(mht* hashtable, Dyninst::Address key, std::set<Dyninst::MachRegister> creg, 
	std::set<Dyninst::MachRegister> zreg, bool initial) {
    //ch = fopen("check.txt", "a");
    bool found = false;
    if ((float)hashtable->count / hashtable->size >= LOAD_FACTOR_THRESHOLD) {
        resize(hashtable);
    }
    mkv *retobj = NULL;

    unsigned long slot = H(key, hashtable->size);

    if (hashtable->table[slot] == NULL) {
        // If the slot is empty, insert the key-value pair
        hashtable->table[slot] = (mkv*)calloc(1, sizeof(mkv));
        hashtable->table[slot]->startaddr = key;
        hashtable->table[slot]->creg = creg;
		hashtable->table[slot]->zreg = zreg;
		hashtable->table[slot]->initial = initial;
        hashtable->table[slot]->next = NULL;
        retobj = hashtable->table[slot];
        hashtable->count++;
    } else {
        // If the slot is not empty, append to the end of the linked list
        mkv* curr = hashtable->table[slot];
        //if(key == 0x7fffffffd9d0 && mmid == 0x19dd)
            //fprintf(ch, "1curr: %p, curr->mid: 0x%lx, curr->key: 0x%lx\n", curr, curr->mid, curr->key);
        if(curr->startaddr == key){
            curr->creg = creg;
			curr->zreg = zreg;
			curr->initial = initial;
            retobj = curr;
            //free(kvp);    
        }else{
            while (curr != NULL) {
                if(curr->startaddr == key){
                    found = true;
                    break;
                }else{
                    if(curr->next != NULL){
                        curr = curr->next;
                    }else{
                        break;
                    }
                }
            }
            if(found){
                curr->creg = creg;
				curr->zreg = zreg;
				curr->initial = initial;
                retobj = curr;
            }else{
                curr->next = (mkv*)calloc(1, sizeof(mkv));
                curr->next->startaddr = key;
				curr->next->creg = creg;
				curr->next->zreg = zreg;
				curr->next->initial = initial;
                retobj = curr->next;
                hashtable->count++;
            }
        }
    }
    return retobj;
}

void destroy(mht* hashtable) {
    for (unsigned long i = 0; i < hashtable->size; i++) {
        mkv* curr = hashtable->table[i];
        while (curr != NULL) {
            mkv* temp = curr;
            curr = curr->next;
            free(temp);
        }
    }
    free(hashtable->table);
    free(hashtable);
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
