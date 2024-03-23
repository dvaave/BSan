#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdbool.h>

#define LOAD_FACTOR_THRESHOLD 0.7
#define GROWTH_FACTOR 2
FILE *ch;
typedef struct mkv {
    unsigned long key;
	unsigned long mid;
    struct mkv* next;
} mkv;

typedef struct {
    unsigned long size;
    unsigned long count;
    mkv** table;
} mht;

uint64 mhash(unsigned long key, unsigned long table_size) {
    // Perform a simple modulo operation for hashing
    return key % table_size;
}

mht* mcreate_hashtable(unsigned long size) {
    mht* hashtable = (mht*)malloc(sizeof(mht));
    hashtable->size = size;
    hashtable->count = 0;
    hashtable->table = (mkv**)malloc(size * sizeof(mkv*));
    for (unsigned long i = 0; i < size; i++) {
        hashtable->table[i] = NULL;
    }
    return hashtable;
}

void mresize(mht* hashtable) {
    unsigned long old_size = hashtable->size;
    unsigned long new_size = old_size * GROWTH_FACTOR;
    mkv** new_table = (mkv**)calloc(new_size, sizeof(mkv*));

    // Rehash all existing key-value pairs into the new table
    for (unsigned long i = 0; i < old_size; i++) {
		mkv* curr = hashtable->table[i];
        while (curr != NULL) {
            mkv* next = curr->next;
            uint64 slot = mhash(curr->key, new_size);
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

mkv* msearch(mht* hashtable, unsigned long key) {
    uint64 slot = mhash(key, hashtable->size);
    mkv* curr = hashtable->table[slot];
    while (curr != NULL) {
        if (curr->key == key) {
            return curr;
        }
        curr = curr->next;
    }
    return NULL;  // Key not found
}

void minsert(mht* hashtable, unsigned long key, unsigned long mmid) {
    //ch = fopen("check.txt", "a");
    bool found = false;
    if ((float)hashtable->count / hashtable->size >= LOAD_FACTOR_THRESHOLD) {
        mresize(hashtable);
    }
    
    uint64 slot = mhash(key, hashtable->size);

    if (hashtable->table[slot] == NULL) {
        // If the slot is empty, insert the key-value pair
        hashtable->table[slot] = (mkv*)malloc(sizeof(mkv));
        hashtable->table[slot]->key = key;
        hashtable->table[slot]->mid = mmid;
        hashtable->table[slot]->next = NULL;
        hashtable->count++;
    } else {
        // If the slot is not empty, append to the end of the linked list
        mkv* curr = hashtable->table[slot];
        //if(key == 0x7fffffffd9d0 && mmid == 0x19dd)
            //fprintf(ch, "1curr: %p, curr->mid: 0x%lx, curr->key: 0x%lx\n", curr, curr->mid, curr->key);
		if(curr->key == key){
			curr->mid = mmid;
            //free(kvp);	
		}else{
			while (curr != NULL) {
				if(curr->key == key){
                    found = true;
                    //if(key == 0x7fffffffd9d0 && mmid == 0x19dd)
                        //fprintf(ch, "3curr: %p, curr->mid: 0x%lx, curr->key: 0x%lx\n", curr, curr->mid, curr->key);
                    break;
                }else{
                    //if(key == 0x7fffffffd9d0 && mmid == 0x19dd)
                        //fprintf(ch, "2curr: %p, curr->mid: 0x%lx, curr->key: 0x%lx\n", curr, curr->mid, curr->key);
                    if(curr->next != NULL){
                        curr = curr->next;
                    }else{
                        break;
                    }
                }
			}
            if(found){
                curr->mid = mmid;
            }else{
                curr->next = (mkv*)malloc(sizeof(mkv));
                curr->next->key = key;
                curr->next->mid = mmid;
                curr->next->next = NULL;
                /*if(key == 0x7fffffffd9d0 && mmid == 0x19dd){
                    fprintf(ch, "curr %p, curr->key 0x%lx, curr->mid: 0x%lx, currnext: %p, curr->next->key 0x%lx, curr->next->mid: 0x%lx, slot 0x%lx, hashsize: 0x%lx\n", 
                        curr,curr->mid, curr->key,curr->next, curr->next->key, curr->next->mid, slot, hashtable->size);
                    mkv* qq = hashtable->table[slot];
                    while (qq->next != NULL) {
                        fprintf(ch, "qq: %p, qq->mid: 0x%lx, qq->key: 0x%lx\n", qq, qq->mid, qq->key);
                        qq = qq->next;
                    }
                }*/
                hashtable->count++;
            }
		}
    }
    /*uint64 kk = 1;
    mkv *ccc = msearch(hashtable, key);
    if(ccc != NULL){
        if(ccc->mid != mmid){
            uint64 checkslot = mhash(key, hashtable->size);
            fprintf(ch, "ccc: %p, insert failed to mem 0x%lx, store id is 0x%lx, but insert id is 0x%lx, slot is 0x%lx, checkslot 0x%lx, hashsize: 0x%lx\n", ccc,key, ccc->mid, mmid, slot, checkslot, hashtable->size);
            mkv* aaa = hashtable->table[slot];
            while (aaa->next != NULL) {
                if(aaa->key == key){
                    printf("aaa %p, failed insert id 0x%lx, current store id 0x%lx of mem 0x%lx\n", aaa,mmid, aaa->mid, aaa->key);
                    //curr->mid = mid;
                    //printf("re store id 0x%lx in mem 0x%lx\n", curr->mid, curr->key);
                    break;
                }else{
                    printf("aaa %p, current store id 0x%lx of mem 0x%lx\n", aaa, aaa->mid, aaa->key);
                }
                kk++;
                aaa = aaa->next;
            }
            //exit(-1);
        }
    }else{
        printf("insert failed\n");
    }
    /*uint64 cslot = mhash(key, hashtable->size);
    mkv* xxx = hashtable->table[cslot];
    if(cslot == 0x59d0){
        uint64 ii = 1;
        while (xxx->next != NULL) {
            if(xxx->key == key){
                fprintf(ch, "store id 0x%lx for mem 0x%lx, mark 0x%lx, goal 0x%lx, slot 0x%lx\n", xxx->mid, xxx->key, ii, kk, slot);
            }else{
                fprintf(ch, "store id 0x%lx for mem 0x%lx, mark 0x%lx, goal 0x%lx, slot 0x%lx\n", xxx->mid, xxx->key, ii, kk, slot);
            }
            ii++;
            xxx = xxx->next;
        }
    }*/
    //fclose(ch);
}



void mdestroy_hashtable(mht* hashtable) {
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

void mhfree(mht* hashtable, unsigned long key){
	mkv* fobj = msearch(hashtable, key);
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
