external bytes_to_string_tag : bytes -> string = "caml_unsafe_string_of_bytes"
external string_length : string -> int = "%string_length"
external bytes_create : int -> bytes = "caml_create_bytes"
external string_blit : string -> int -> bytes -> int -> int -> unit
                     = "caml_blit_string" [@@noalloc]

let ( ^ ) s1 s2 =
  let l1 = string_length s1 and l2 = string_length s2 in
  let s = bytes_create (l1 + l2) in
  string_blit s1 0 s 0 l1;
  string_blit s2 0 s l1 l2;
  bytes_to_string_tag s



let build_numeral n =
  let rec helper n =
    if n = 0 then {|"x")))|}
    else
      {|App ("f", |} ^ (helper (n-1)) ^ ")"
    in 
    {|Lam ("f", (Lam("x", |} ^ (helper n);;

let build_pair x y z = 
  "Lam (" ^ x ^ ", Lam (" ^ y ^ ", Lam(" ^ z ^ ", App(App(" ^ x ^ ", " ^ z ^ "), " ^ y ^ "))))";;
(* Lam (    x    , Lam (    y    , Lam(    z    , App(App(    x    ,     z    ),     y    ))))*)

print_endline (build_pair (build_numeral 1) (build_numeral 2) {|Var "z"|})
