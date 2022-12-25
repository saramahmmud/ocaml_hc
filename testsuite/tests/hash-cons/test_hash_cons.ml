(* TEST
   modules = "hash_cons_prims.c"
*)

external test1: string -> string -> unit = "test_string_present"
external test2: string -> unit = "test_string_not_present"
external test3: string -> string -> unit = "test_linked_list_works"

let x = "test string"
let x_dup = "test string"
let y = "another test string"

let () = test1 x x
let () = test2 x
let () = test3 x y
