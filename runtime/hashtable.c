#include "caml/alloc.h"
#include "caml/compare.h"
#include "caml/hashtable.h"
#include "caml/memory.h"
#include "caml/mlvalues.h"
#include "caml/weak.h"
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>

value string_to_hash_val(const char* string, int size) {
    CAMLparam0();
    uintnat i = 0;
    for (int j=0; string[j]; j++)
        i += string[j];
    CAMLreturn(Val_long(i));
}

value create_table(int size) {
    CAMLparam0();
    // Creates a new HashTable of size 'size' in bytes
    //HashTable* table = (HashTable*) caml_stat_alloc_noexc (sizeof(HashTable));
    CAMLlocal2(table, item_array);
    //CAMLlocalN(item_array, size);
    item_array = caml_alloc(size, 0);
    for (int i=0; i<size; i++) {
      Store_field(item_array, i, Val_unit);
    }
 
    table = caml_alloc(3, 0);
    
    printf("\n\nCreating Table\n\n");
    fflush(stdout);
   
    //Field(table, 0) = item_array;
    Store_field(table, 0, item_array);
    //Field(table, 1) = Val_int(size);
    Store_field(table, 1, Val_int(size));
    //Field(table, 2) = Val_int(0);
    Store_field(table, 2, Val_int(0));
    for (int ind = 0; ind<10; ind++){
        //printf("\n index: %d, item: %ld", ind, Field(table->items, ind));
	printf("\n index: %d, item: %ld", ind, Field(Field(table, 0), ind));
	fflush(stdout);
    }
    CAMLreturn(table);
};

value create_item(value eph_key, value eph_data) {
    CAMLparam2(eph_key, eph_data);
    /* Creates a new hash table item which is represented
    as an OCaml value with 2 fields.
    
    The tag is 0 to indicate that it is a structured block 
    where each field is a value.
    
    The first field is an OCaml ephmeron which has one key (weak 
    pointer) which is the pointer to the hash-consed value and 
    one data (strong pointer) which is the hash value of the
    hash-consed value.

    The second field is a pointer to the 'next' item in the
    hash table, forming a linked list. This is used to resolve 
    collisions.
    */
    CAMLlocal2(ephemeron, item);
    ephemeron = caml_ephemeron_create(1);
    caml_ephemeron_set_key(ephemeron, 0, eph_key);
    caml_ephemeron_set_data(ephemeron, eph_data);
    item = caml_alloc_small (2, 0);
    Field(item, 0) = ephemeron;
    Field(item, 1) = Val_unit;
   
    
    printf("\n\n creating item: %ld, ephemeron: %ld, next: %ld, eph_key: %s\n\n", item, Field(item, 0), Field(item, 1), String_val(eph_key));
    fflush(stdout);
    CAMLreturn(item);
}

void ht_insert(value table, value pointer) {
  CAMLparam2(table, pointer);
  CAMLlocal3(hash_val, item, cur_item);
    // Inserts a new item into the hash table
  //printf("\n\n table count: %d \n\n", table->count);
  printf("\n\n table count: %ld \n\n", Field(table, 2));fflush(stdout);
  if ((Tag_val(pointer) == String_tag)){
        const char* string = String_val(pointer);
	int index;
        //value hash_val = string_to_hash_val(string, table->size);
	hash_val = string_to_hash_val(string, Field(table, 1));
        item = create_item(pointer, hash_val);
	index = abs(hash_val) % Field(table, 1);
	// int index = abs(hash_val) % table->size;
        //value cur_item = Field(table->items, index);
	cur_item = Field(Field(table, 0), index);
	
	//insert the item at the front of the linked list
        //Field(item, 1) = cur_item;
	caml_modify(&Field(item, 1), cur_item);
	//Field(table->items, index) = item;
	//Field(Field(table, 0), index) = item;
	caml_modify(&Field(Field(table, 0), index), item);  
	
	printf("\n\ninserting item %ld at index %d\n\n", item, index);
	//printf("\n\nget field at index %d: %ld\n\n", index, Field(table->items, index));
	printf("\n\nget field at index %d: %ld\n\n", index, Field(Field(table, 0), index));
        caml_modify(&Field(table, 2), Val_int(Int_val(Field(table, 2))+1));
    }
  CAMLreturn0;
}

value ht_search(value table, value pointer) {
  
  CAMLparam2(table, pointer);
  CAMLlocal4(existing_pointer, data, hash_val, item);
    /* Searches for a value in the hashtable and returns the 
    stored pointer if it exists.
    Returns the OCaml value encoding of false if it doesn't exist.
    */
  printf("\nsearch_function\n");
  existing_pointer = caml_alloc(1, 0);
  printf("\nstored field1\n");
  Store_field(existing_pointer, 0, Val_unit);
  
  data = caml_alloc(1, 0);
  Field(data, 0) = Val_unit;
  printf("\nstored field1\n");

    if (Tag_val(pointer) == String_tag){
        const char* string = String_val(pointer);
	//value hash_val = string_to_hash_val(string, table->size);
        //int index = abs(hash_val) % table->size;
        //value item = Field(table->items, index);
	int index;
	printf("searching: %s", string);
	hash_val = string_to_hash_val(string, Field(table, 1));
	index = abs(hash_val) % Field(table, 1);
        item = Field(Field(table, 0), index);
	
	printf("\n\nsearching for item: %ld\n\n", pointer);
	for (int ind = 0; ind<10; ind++){
	  //printf("\n index: %d, item: %ld", ind, Field(table->items, ind));
	  printf("\n index: %d, item: %ld", ind, Field(Field(table, 0), ind));
	}
	
        while (item != Val_unit) {
	  printf("\n\nseach starting at index %d with  item: %ld\n\n", index, item);
	  fflush(stdout);
            //if data is set
            if (caml_ephemeron_get_data(Field(item, 0), &data)){
                //and data is the same as the hash_val
                if (data == hash_val){
                    //return the pointer
                    if (caml_ephemeron_get_key(Field(item, 0), 0, &existing_pointer)){
		      CAMLreturn(existing_pointer);
                    }
                }
            }
            //if data is not set, check the next item
            item = Field(item, 1);
        }
    }
    CAMLreturn(Val_false);
}
