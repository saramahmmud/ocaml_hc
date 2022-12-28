#include "mlvalues.h"

typedef struct HashTable HashTable;

struct HashTable {
    /* Hash table items are stored in the heap but marked as generational global roots*/
    value items;
    int size;
    int count;
};

/* Hash table to store hash-consed values*/
extern HashTable* hc_table;

/*The hashTable is stored outside of the heap with pointers to hashtable items in the heap*/
HashTable* create_table(int size);
void ht_insert(HashTable* table, value pointer);
value ht_search(HashTable* table, value pointer);