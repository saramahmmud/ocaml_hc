#include "caml/compare.h"
#include "caml/hashtable.h"
#include "caml/memory.h"
#include "caml/mlvalues.h"
#include "caml/weak.h"
#include <stdlib.h>

value string_to_hash_val(const char* string, int size) {
    uintnat i = 0;
    for (int j=0; string[j]; j++)
        i += string[j];
    return Val_long(i);
}

HashTable* create_table(int size) {
    // Creates a new HashTable of size 'size' in bytes
    HashTable* table = (HashTable*) caml_stat_alloc_noexc (sizeof(HashTable));
    table->size = size;
    table->count = 0;
    table->items = (Ht_item**) caml_stat_alloc_noexc (size * sizeof(Ht_item*));
    for (int i=0; i<table->size; i++)
        table->items[i] = NULL;
    return table;
};

Ht_item* create_item(value eph_key, value eph_data) {
    // Creates a pointer to a new hash table item
    Ht_item* item = (Ht_item*) caml_stat_alloc_noexc (sizeof(Ht_item));

    value ephemeron = caml_ephemeron_create(1);
    caml_ephemeron_set_key(ephemeron, 0, eph_key);
    caml_ephemeron_set_data(ephemeron, eph_data);

    item->eph = ephemeron;
    item->next = NULL;

    return item;
}

void ht_insert(HashTable* table, value pointer) {
    // Inserts a new item into the hash table
    if (Tag_val(pointer) == String_tag){
        const char* string = String_val(pointer);
        value hash_val = string_to_hash_val(string, table->size);
        Ht_item* item = create_item(pointer, hash_val);

        intnat index = abs(hash_val) % table->size;
        Ht_item* cur_item = table->items[index];
        if (cur_item == NULL) {
            // If the index is empty, insert the item
            table->items[index] = item;
        } else {
            // If the index is not empty, insert the item at the end of the linked list
            while (cur_item->next != NULL)
                cur_item = cur_item->next;
            cur_item->next = item;
        }
        table->count++;
    }
}

value ht_search(HashTable* table, value pointer) {
    // Searches for a value in the hashtable and returns the stored pointer if it exists
    // returns the OCaml value encoding of false if it doesn't exist.
    value existing_pointer;
    if (Tag_val(pointer) == String_tag){
        const char* string = String_val(pointer);
        value hash_val = string_to_hash_val(string, table->size);
        int index = abs(hash_val) % table->size;
        Ht_item* item = table->items[index];

        if (item != NULL) {
            value* data;
            if (caml_ephemeron_get_data(item->eph, data)){
                if (*data == hash_val)
                    if (caml_ephemeron_get_key(item->eph, 0, &existing_pointer)){
                        return existing_pointer;
                    }
            }
            else{
                return Val_false;
            }
        }
        else {
            while (item->next != NULL) {
                item = item->next;
                value* data;
                if (caml_ephemeron_get_data(item->eph, data)){
                    if (*data == hash_val)
                        if (caml_ephemeron_get_key(item->eph, 0, &existing_pointer)){
                        return existing_pointer;
                    }
                }
                else{
                    return Val_false;
                }
            }
        }
    }
    return Val_false;
}