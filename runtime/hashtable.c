#define CAML_INTERNALS //is this needed?

#include "caml/alloc.h"
#include "caml/hashtable.h"
#include "caml/memory.h"
#include "caml/mlvalues.h"
#include "caml/weak.h"
#include "caml/gc.h"
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <string.h>

int debug = 0;

long string_to_hash_val(value string) {
    mlsize_t length = caml_string_length(string);
    uintnat i = 0;
    for (int j=0; j<length; j++)
        i += Byte_u(string, j);
    return (long) i;
}

int caml_compare_strings(value s1, value s2){
    mlsize_t len1 = caml_string_length(s1);
    mlsize_t len2 = caml_string_length(s2);

    if (len1!=len2){
      return 0;
    }

    for (mlsize_t i=0; i<len1; i++){
      if (Byte_u(s1, i) != Byte_u(s2, i)){
         return 0;
      }
    }
    return 1;
}

value create_table(int size) {
    CAMLparam0();
    // Creates a new HashTable of size 'size' in bytes
    // HashTable* table = (HashTable*) caml_stat_alloc_noexc (sizeof(HashTable));
    CAMLlocal2(table, item_array);
    if (debug) printf("\n\nCreating Table\n\n");
    item_array = (value) caml_alloc_shr_for_minor_gc(size, 0, Make_header(2, 0, Caml_white));
    for (int i=0; i<size; i++) {
      Field(item_array, i) =Val_unit;
    }

    table = (value) caml_alloc_shr_for_minor_gc(3, 0, Make_header(2, 0, Caml_white));  

    Field(table, 0) = item_array;
    //Store_field(table, 0, item_array);
    Field(table, 1) = Val_int(size);
    //Store_field(table, 1, Val_int(size));
    Field(table, 2) = Val_int(0);
    //Store_field(table, 2, Val_int(0));
    
    if (debug) {
      for (int ind = 0; ind<size; ind++){
        printf("\n index: %d, item: %lx", ind, Field(Field(table, 0), ind));
        fflush(stdout);
      }
      printf("\n\n table size,  count: %d, %d \n\n", Int_val(Field(table, 1)), Int_val(Field(table, 2)));fflush(stdout);
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
    item = caml_alloc_shr_for_minor_gc(2, 0, Make_header(2, 0, Caml_white));
    Field(item, 0) = ephemeron;
    Field(item, 1) = Val_unit;
   
    
    if (debug) {
      printf("creating item: %lx, ephemeron: %lx, next: %lx, eph_key: %s\n", item, Field(item, 0), Field(item, 1), String_val(eph_key));
      fflush(stdout);
    }
    CAMLreturn(item);
}

void ht_insert(value table, value pointer) {
  CAMLparam2(table, pointer);
  CAMLlocal2(item, cur_item);
  long hash_val;
  // Inserts a new item into the hash table
  if (debug) {
    printf("table count: %d \n", Int_val(Field(table, 2)));
    fflush(stdout);
  }
  if ((Tag_val(pointer) == String_tag)){
    int index;
    hash_val = string_to_hash_val(pointer);
    item = create_item(pointer, hash_val);
    index = abs(hash_val) % Int_val(Field(table, 1));
    cur_item = Field(Field(table, 0), index);
    

    caml_modify(&Field(item, 1), cur_item);
    caml_modify(&Field(Field(table, 0), index), item);  
    
    if (debug) {
      printf("inserting item %lx at index %d\n", item, index);
      printf("get field at index %d: %lx\n", index, Field(Field(table, 0), index));
    }

    caml_modify(&Field(table, 2), Val_int(Int_val(Field(table, 2))+1));

    }
  if (debug) printf("inserted\n");
  CAMLreturn0;
}

value ht_search(value table, value pointer) {
  CAMLparam2(table, pointer);
  CAMLlocal4(existing_pointer, data,item, saras_test);
  long hash_val;
  /* Searches for a value in the hashtable and returns the 
  stored pointer if it exists.
  Returns the OCaml value encoding of false if it doesn't exist.
  */
  if (debug) {
    printf("\nsearch_function\n");
    printf("\nTable size, count: %d, %d\n", Int_val(Field(table, 1)), Int_val(Field(table, 2)));
  }

  existing_pointer = caml_alloc_shr_for_minor_gc(1, 0, Make_header(1, 0, Caml_white));
  Field(existing_pointer, 0) = Val_unit;
  
  data = caml_alloc_shr_for_minor_gc(1, 0, Make_header(1, 0, Caml_white));
  Field(data, 0) = Val_unit;

    if (Tag_val(pointer) == String_tag){
        int index;
        hash_val = string_to_hash_val(pointer);
        index = abs(hash_val) % Int_val(Field(table, 1));
        item = Field(Field(table, 0), index);
	
        if (debug) {
          printf("\n\nsearching for string %s, pointer %lx\n\n", String_val(pointer), pointer);
          for (int ind = 0; ind<Int_val(Field(table, 1)); ind++){
            printf("index: %d, item: %lx\n", ind, Field(Field(table, 0), ind));
          }
        }
	
        while (item != Val_unit) {
            // if data is set
            if (caml_ephemeron_get_data(Field(item, 0), &data)){
                // and data is the same as the hash_val
                if (data == hash_val){
                  if (debug) printf("eph data = hash_val\n");
                    // if the key is set
                    if (caml_ephemeron_get_key(Field(item, 0), 0, &existing_pointer)){
                        if (debug) printf("eph key found: %s\n", String_val(existing_pointer));
                        // and the key matches the string we are searching for
                        if (caml_compare_strings(existing_pointer, pointer)){
                          if (debug) printf("strings match\n");
                          // return the pointer
                          CAMLreturn(existing_pointer);
                        }
		                    
                    }
                }
            }
            // otherwise, check the next item
            item = Field(item, 1);
        }
    }
    CAMLreturn(Val_false);
}
