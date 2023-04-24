#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include "caml/hashtable.h"
#include "caml/hash.h"
#include "caml/mlvalues.h"
#include "caml/alloc.h"

void test_present (value v1, value v2){
    value table = create_table(10);
    value hash = caml_hash_generic(Val_int(10), Val_int(1000), SEED, v1);
    ht_insert(table, v1, hash);
    value stored_pointer = ht_search(table, v2);
    assert(stored_pointer == v1);
}

void test_not_present (value v){
    value table = create_table(10);
    value pointer = ht_search(table, v);
    assert(pointer == Val_false);
}

void test_linked_list_works (value v1, value v2){
    value table = create_table(1);
    value hash1 = caml_hash_generic(Val_int(10), Val_int(1000), SEED, v1);
    value hash2 = caml_hash_generic(Val_int(10), Val_int(1000), SEED, v2);
    ht_insert(table, v1, hash1);
    ht_insert(table, v2, hash2);
    value p1 = ht_search(table, v1);
    value p2 = ht_search(table, v2);
    assert((v1 == p1) && (v2 == p2));
}