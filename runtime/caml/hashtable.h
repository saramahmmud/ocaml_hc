#include "mlvalues.h"

typedef struct HashTable HashTable;

struct HashTable {
    /* 'items' is an array stored in the heap but marked as a generational global root*/
    value items;
    /* For now these fields are not used but in future I may add resizing of the hash table
    depending on capacity. */
    int size;
    int count;
};

/* Hash table to store hash-consed values*/
extern HashTable* hc_table;

/*The hashTable is stored outside of the heap*/
HashTable* create_table(int size);
void ht_insert(HashTable* table, value pointer);
value ht_search(HashTable* table, value pointer);