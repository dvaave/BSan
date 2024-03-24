#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>

#define LOAD_FACTOR_THRESHOLD 0.7
#define GROWTH_FACTOR 2

typedef struct ckv {
    unsigned long key;
	unsigned long cpc;//dynamic pc
    struct ckv* next;
} ckv;

typedef struct {
    unsigned long size;
    unsigned long count;
    ckv** table;
} cht;

int chash(unsigned long key, unsigned long table_size) {
    // Perform a simple modulo operation for hashing
    return key % table_size;
}

cht* ccreate_hash(unsigned long size) {
    cht* hashtable = (cht*)malloc(sizeof(cht));
    hashtable->size = size;
    hashtable->count = 0;
    hashtable->table = (ckv**)malloc(size * sizeof(ckv*));
    for (unsigned long i = 0; i < size; i++) {
        hashtable->table[i] = NULL;
    }
    return hashtable;
}

void cresize(cht* hashtable) {
    unsigned long old_size = hashtable->size;
    unsigned long new_size = old_size * GROWTH_FACTOR;
    ckv** new_table = (ckv**)calloc(new_size, sizeof(ckv*));

    // Rehash all existing key-value pairs into the new table
    for (unsigned long i = 0; i < old_size; i++) {
		ckv* curr = hashtable->table[i];
        while (curr != NULL) {
            ckv* next = curr->next;
            int slot = chash(curr->key, new_size);
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

bool iscall(cht* hashtable, unsigned long pc, unsigned long addr){
    for (unsigned long i = 0; i < hashtable->size; i++){
        ckv* curr = hashtable->table[i];
        while (curr != NULL){
            ckv* next = curr->next;
            unsigned long cadd = curr->key;
            if(cadd > pc && cadd <= addr){
                return true;
                break;
            }
            curr = next;
        }
        return false;
    }
}

void cinsert(cht* hashtable, unsigned long key, unsigned long cpc) {
    bool found = false;
    if ((float)hashtable->count / hashtable->size >= LOAD_FACTOR_THRESHOLD) {
        cresize(hashtable);
    }

    int slot = chash(key, hashtable->size);
    ckv* kvp = (ckv*)malloc(sizeof(ckv));
    kvp->key = key;
    kvp->cpc = cpc;
    kvp->next = NULL;

    if (hashtable->table[slot] == NULL) {
        // If the slot is empty, insert the key-value pair
        hashtable->table[slot] = kvp;
        hashtable->count++;
    } else {
        // If the slot is not empty, append to the end of the linked list
        ckv* curr = hashtable->table[slot];
		if(curr->key == key){
            curr->cpc = cpc;
            free(kvp);	
		}else{
			while (curr != NULL) {
				if(curr->key == key){
                    found = true;
                    free(kvp);
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
                curr->cpc = cpc;
            }else{
                curr->next = kvp;
                hashtable->count++;
            }
		}
    }
}

ckv* csearch(cht* hashtable, unsigned long key) {
    int slot = chash(key, hashtable->size);
    ckv* curr = hashtable->table[slot];
    while (curr != NULL) {
        if (curr->key == key) {
            return curr;
        }
        curr = curr->next;
    }
    return NULL;  // Key not found
}

void cdestroy_hashtable(cht* hashtable) {
    for (unsigned long i = 0; i < hashtable->size; i++) {
        ckv* curr = hashtable->table[i];
        while (curr != NULL) {
            ckv* temp = curr;
            curr = curr->next;
            free(temp);
        }
    }
    free(hashtable->table);
    free(hashtable);
}

void cfree(cht* hashtable, unsigned long key){
	ckv* fobj = csearch(hashtable, key);
	if(fobj != NULL){
		fobj->key = 0;
	}else{
		//printf("double free detected\n");
        //exit(-1);
	}
}

/*int main() {
    idht* hashtable = idcreate_hashtable(0x8);

    idinsert(hashtable, 123, 1001, 121321312);
    idinsert(hashtable, 987, 2002, 212321321);
    idinsert(hashtable, 5432, 3003, 321312321);
    idinsert(hashtable, 9876532, 4004, 421321321);  // Overwriting value for the same key
	
    idkv* obj = idsearch(hashtable, 123);
    if (obj != NULL) {
        printf("ID found: %lu, %lu\n", obj->addr, obj->osize);
    } else {
        printf("ID not found.\n");
    }
	idfree(hashtable, 123);
	obj = idsearch(hashtable, 123);
	if (obj != NULL) {
        printf("ID found: %lu, %lu\n", obj->addr, obj->osize);
    } else {
        printf("ID not found.\n");
    }
    idestroy_hashtable(hashtable);

    return 0;
}*/
