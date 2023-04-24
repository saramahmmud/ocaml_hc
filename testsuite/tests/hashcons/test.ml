(*TEST
   modules = "hash-cons-prims.c"
*)

external test_present: 'a -> 'a -> unit = "test_present"
external test_not_present: 'a -> unit = "test_not_present"
external test_linked_list_works: 'a -> 'a -> unit = "test_linked_list_works"

type s =
| Foo of bool
| Baz of int
| Bar of string

type t =
CoolConstructor of s * s [@@hashconsed]

let createT a = CoolConstructor ((Foo (a mod 2 == 0)), (Baz (a mod 3)))

let a = createT 2
let b = createT 2

let c = "test string"
let c_dup = "test string"
let d = "another test string"

let () = test_present c c_dup
let () = test_not_present c
let () = test_present a b
let () = test_not_present a
let () = test_linked_list_works c d 
