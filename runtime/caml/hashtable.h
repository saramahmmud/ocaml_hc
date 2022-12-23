#include "mlvalues.h"

typedef struct Ht_item Ht_item;

struct Ht_item {
    value eph;
    Ht_item* next;
};

typedef struct HashTable HashTable;

struct HashTable {
    /* Contains an array of pointers to items
    Ht_item** items == Ht_item* *items == Ht_item* items[0]
    */
    Ht_item** items;
    int size;
    int count;
};

/* Hash table to store hash-consed values*/
extern HashTable* caml_hc_table;

HashTable* create_table(int size);
void ht_insert(HashTable* table, value block);
value ht_search(HashTable* table, value block);