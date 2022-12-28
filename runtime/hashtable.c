#include "caml/alloc.h"
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
    value item_array = caml_alloc_small (size, 0);
    caml_register_generational_global_root(&item_array);
    for (int i=0; i<size; i++)
        Field(item_array, i) = Val_unit;
    table->items = item_array;
    table->size = size;
    table->count = 0;
    return table;
};

value create_item(value eph_key, value eph_data) {
    // Creates a new hash table item

    value ephemeron = caml_ephemeron_create(1);
    value item = (value) caml_alloc_small (2, 0);
    caml_ephemeron_set_key(ephemeron, 0, eph_key);
    caml_ephemeron_set_data(ephemeron, eph_data);
    Field(item, 0) = ephemeron;
    Field(item, 1) = Val_unit;

    return item;
}

void ht_insert(HashTable* table, value pointer) {
    // Inserts a new item into the hash table
    if (Tag_val(pointer) == String_tag){
        const char* string = String_val(pointer);
        value hash_val = string_to_hash_val(string, table->size);
        value item = create_item(pointer, hash_val);

        int index = abs(hash_val) % table->size;
        value cur_item = Field(table->items, index);
        if (cur_item == Val_unit) {
            // If the index is empty, insert the item
            Field(table->items, index) = item;
        } else {
            // If the index is not empty, insert the item at the end of the linked list
            while (Field(cur_item, 1) != Val_unit)
                cur_item = Field(cur_item, 1);
            Field(cur_item, 1) = item;
        }
        table->count++;
    }
}

value ht_search(HashTable* table, value pointer) {
    // Searches for a value in the hashtable and returns the stored pointer if it exists
    // returns the OCaml value encoding of false if it doesn't exist.
    value existing_pointer;
    value data = caml_alloc_small(sizeof(value), 0);
    data = Val_unit;
    if (Tag_val(pointer) == String_tag){
        const char* string = String_val(pointer);
        value hash_val = string_to_hash_val(string, table->size);
        int index = abs(hash_val) % table->size;
        value item = Field(table->items, index);

        if (item != Val_unit) {
            //if data is set
            if (caml_ephemeron_get_data(Field(item, 0), &data)){
                //and data is the same as the hash_val
                if (data == hash_val){
                    //return the pointer
                    if (caml_ephemeron_get_key(Field(item, 0), 0, &existing_pointer)){
                        return existing_pointer;
                    }
                    else{
                        //If the key (pointer) has been collected, keep searching linked list for now
                        while (Field(item, 1) != Val_unit) {
                            item = Field(item, 1);
                            //if data is set
                            if (caml_ephemeron_get_data(Field(item, 0), &data)){
                                //and data is the same as the hash_val
                                if (data == hash_val){
                                    //return the pointer
                                    if (caml_ephemeron_get_key(Field(item, 0), 0, &existing_pointer)){
                                        return existing_pointer;
                                    }
                                }
                            }
                        }
                    }
                }
                else{
                    //If the hash_val isn't the same, keep searching linked list
                    while (Field(item, 1) != Val_unit) {
                        item = Field(item, 1);
                        //if data is set
                        if (caml_ephemeron_get_data(Field(item, 0), &data)){
                            //and data is the same as the hash_val
                            if (data == hash_val){
                                //return the pointer
                                if (caml_ephemeron_get_key(Field(item, 0), 0, &existing_pointer)){
                                    return existing_pointer;
                                }
                            }
                        }
                    }
                }
            }
            else{
                //If the data (hash_val) has been collected???, keep searching linked list for now
                while (Field(item, 1) != Val_unit) {
                    item = Field(item, 1);
                    //if data is set
                    if (caml_ephemeron_get_data(Field(item, 0), &data)){
                        //and data is the same as the hash_val
                        if (data == hash_val){
                            //return the pointer
                            if (caml_ephemeron_get_key(Field(item, 0), 0, &existing_pointer)){
                                return existing_pointer;
                            }
                        }
                    }
                }
            }
        }
    }
    return Val_false;
}