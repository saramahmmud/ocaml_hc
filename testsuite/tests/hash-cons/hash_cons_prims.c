#include <stdio.h>
#include <stdlib.h>
#include "caml/hashtable.h"
#include "caml/mlvalues.h"
#include "caml/alloc.h"
 
void test_string_present (value v1, value v2){
    HashTable* table = create_table(10);
    ht_insert(table, v1);
    value pointer = ht_search(table, v2);
    char* stored_pointer = Bp_val(v1);
    char* found_pointer = Bp_val(pointer);
    if (stored_pointer == found_pointer)
        printf("The correct pointer was returned\n");
    else
        printf("Test failed\n");
}

void test_string_not_present (value v){
    HashTable* table = create_table(10);
    value pointer = ht_search(table, v);
    if (pointer == Val_false)
        printf("The string that was not inserted was not found\n");
    else
        printf("Test failed\n");
}

void test_linked_list_works (value v1, value v2){
    HashTable* table = create_table(1);
    ht_insert(table, v1);
    ht_insert(table, v2);
    value p1 = ht_search(table, v1);
    value p2 = ht_search(table, v2);
    char* stored1 = Bp_val(p1);
    char* stored2 = Bp_val(p2);
    char* found1 = Bp_val(v1);
    char* found2 = Bp_val(v2);
    if (stored1 == found1 && stored2 == found2)
        printf("The correct pointers were returned\n");
    else
        printf("Test failed\n");
}