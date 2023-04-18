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

type id = string

type exp =
    Var of id
  | Lam of id * exp
  | App of exp * exp

(* generates a fresh variable name *)
let newvar =
  let x = ref 0 in
  fun () -> 
    let c = !x in
    incr x;
    "v"^(string_of_int c)

(* computes the free (non-bound) variables in e *)
let rec fvs e =
  match e with
      Var x -> [x]
    | Lam (x,e) -> List.filter (fun y -> x <> y) (fvs e)
    | App (e1,e2) -> (fvs e1) @ (fvs e2)
;;

(* substitution: subst e y m means 
  "substitute occurrences of variable y with m in the expression e" *)
let rec subst e y m =
  match e with
    | Var x -> 
      if y = x then m (* replace x with m *)
      else e (* variables don't match: leave x alone *)
    | App (e1,e2) -> App (subst e1 y m, subst e2 y m)
    | Lam (x,e) ->
      if y = x then (* don't substitute under the variable binder *)
      Lam(x,e)
      else if not (List.mem x (fvs m)) then (* no need to alpha convert *)
      Lam (x, subst e y m)
      else (* need to alpha convert *)
      let z = newvar() in (* assumed to be "fresh" *)
      let e' = subst e x (Var z) in (* replace x with z in e *)
      Lam (z,subst e' y m) (* substitute for y in the adjusted term, e' *)

(*
   
Below is my implementation of beta normal order reduction
- it does only one step at a time

bigstep_reduce will continue to reduce until a normal form is reached
- can optionally see how many reductions this took
*)


let rec reduce e =
  match e with
  | App (Lam (x,e), e2) -> (subst e x e2)  (* direct beta rule *)
  | App (e1, e2) ->
    let e1' = reduce e1 in
    if e1' <> e1 then App(e1', e2)
    else 
      let e2' = reduce e2 in App(e1, e2')
  | Lam (x,e) -> Lam (x, reduce e) (* reduce under the lambda (!) *)
  | _ -> e

let rec bigstep_reduce e =
  let e' = reduce e in
  if e' = e then e
  else bigstep_reduce e'


let bigstep_reduce_with_count e =
  let rec helper e count =
    let e' = reduce e in
    if e' = e then (e, count)
    else helper e' (count+1)
  in helper e 0

(* pretty printing *)

open Format;;

let ident = print_string;;
let kwd = print_string;;

let rec print_exp0 = function
  | Var s ->  ident s
  | lam -> open_hovbox 1; kwd "("; print_lambda lam; kwd ")"; close_box ()

and print_app = function
  | e -> open_hovbox 2; print_other_applications e; close_box ()

and print_other_applications f =
  match f with
  | App (f, arg) -> print_app f; print_space (); print_exp0 arg
  | f -> print_exp0 f

and print_lambda = function
  | Lam (s, lam) ->
      open_hovbox 1;
      kwd "\\"; ident s; kwd "."; print_space(); print_lambda lam;
      close_box()
  | e -> print_app e;;

let num n = 
  let rec helper n =
    if n= 0 then Var "x"
    else
      App(Var "f", (helper (n-1)))
    in Lam("f", Lam ("x", (helper n)));;

(*Y*)
let y = Lam("f", App(Lam("x", App(Var"f", App(Var "x", Var"x"))), Lam("x", App(Var"f", App(Var "x", Var"x")))))

let id = Lam("x", Var "x");;

(*Booleans*)
let t = Lam("a", Lam("b", Var "a"));;
let f = Lam("a", Lam("b", Var "b"));;
let logical_not = Lam("b", App(App(Var "b", f), t))
let logical_and = Lam("x", Lam("y", App(App(Var"x", Var"y"), f)))

(*arithmetic*)
let zero = num 0
let isZero = Lam("n", App(App(Var"n", Lam("x", f)), t))
let succ = Lam("n", Lam("f", Lam("x", App(Var"f", App(App(Var"n", Var"f"), Var"x")))))
let pred = Lam("n", Lam("f", Lam("x", App(App(App(Var"n", Lam("g", Lam("h", App(Var"h", App(Var"g", Var"f"))))), Lam("u", Var "x")), Lam("u", Var "u")))))
let subtract = Lam("m", Lam("n", App(App(Var"n", pred), Var"m")))
let leq = Lam("m", Lam("n", App(isZero, App(App(subtract, Var"m"), Var"n"))))
let gre = Lam("m", Lam("n", App(logical_not, App(App(leq, Var"m"), Var"n"))))
let eq = Lam("m", Lam("n", App(App(logical_and, App(App(leq, Var"m"), Var"n")), App(App(leq, Var"n"), Var"m"))))


(*Pairs*)
let pair = Lam("a", Lam("b", Lam ("z", App(App(Var "z", Var "a"), Var "b"))))
let first = Lam("p", App(Var "p", Lam("x", Lam("y", Var "x"))))
let second = Lam("p", App(Var "p", Lam("x", Lam("y", Var "y"))))


(*Lists*)
let empty = Lam("f", Lam("l", Var "f"))
let cons = Lam("h", Lam("t", Lam("f", Lam("l", App(App(Var"l", Var"h"), Var"t")))))

let head = Lam("l", App(App(Var"l", f), t))
let tail = Lam("l", App(App(Var"l", f), f))
let isEmpty = Lam("l", App(App(Var "l", t), Lam("x", Lam("y", f))))

let flip = Lam("p", Lam("x", Lam("y", App(App(Var"p", Var"y"), Var"x"))))

let rec list_builder = function
  | [] -> empty
  | h::t -> App(App(cons, (num h)), (list_builder t))

(*Find church numeral x in list l
  - it returns the index of the item in the list if it exists
  - if the item is not in the list it returns the empty list, i.e. Lam ("f", Lam ("l", Var "f"))
*)
let fFind = Lam("f", Lam("x", Lam("l", Lam("c", App(App(App(isEmpty, Var"l"), empty), App(App(App(App(eq, Var"x"), App(head, Var"l")), Var"c"), App(App(App(Var"f", Var"x"), App(tail, Var"l")), App(succ, Var"c"))))))))
let find = Lam("x", Lam("l", App(App(App(App(y, fFind), Var"x"), Var"l"), zero)))

(*Get list element at index i*)
let fGet = Lam("f", Lam("i", Lam("l", Lam ("c", App(App(App(isEmpty, Var"l"), empty), App(App(App(App(eq, Var"i"), Var"c"), App(head, Var"l")), App(App(App(Var"f", Var"i"), App(tail, Var"l")), App(succ, Var"c"))))))))
let get = Lam("i", Lam("l", App(App(App(App(y, fGet), Var"i"), Var"l"), zero)))

(*Merge lists x and y*)
let fMerge = Lam("f", Lam("x", Lam("y", App(App(Var"x", Var"y"), Lam("h", Lam("t", App(App(cons, Var"h"), App(App(Var"f", Var"t"), Var"y"))))))))
let merge = App(y, fMerge)

(*Reverse list l*)
let fReverse = Lam("f", Lam("l", Lam("r", App(App(App(isEmpty, Var"l"), Var"r"), App(App(Var"f", App(tail, Var"l")), App(App(cons, App(head, Var"l")), Var"r"))))))
let reverse = Lam("l", App(App(App(y, fReverse), Var"l"), empty))

(*Remove elements of list l that satisfy condition p*)
let fRemove = Lam("f", Lam("p", Lam("l", App(App(Var"l", empty), Lam("h", Lam("t", App(App(App(App(Var"p", Var"h"), id), App(cons, Var"h")), App(App(Var"f", Var"p"), Var"t"))))))))
let remove = App(y, fRemove)

(*quick sort a list l of Church numerals in ascending order*)
let fQuickSort = Lam("f", Lam("l", App(App(Var"l", empty), Lam("h", Lam("t", App(App(merge, App(Var"f", App(App(remove, App(App(flip, gre), Var"h")), Var"t"))), App(App(cons, Var"h"), App(Var"f", App(App(remove, App(App(flip, leq), Var"h")), Var"t")))))))))
let quickSort = App(y, fQuickSort)


let my_list = bigstep_reduce (list_builder  [9; 1; 4; 2; 7; 6])
let sort_with_count = bigstep_reduce_with_count (App(quickSort, my_list))

(* TESTS
fvs (Var "x") = ["x"];;
fvs (Lam ("x",Var "y")) = ["y"];;
fvs (Lam ("x",Var "x")) = [];;
fvs (App (Lam ("x", Var "z"), Var "y")) = ["z"; "y"];;

let m1 =  (App (Var "x", Var "y"));;
let m2 = (App (Lam ("z",Var "z"), Var "w"));;
let m3 = (App (Lam ("z",Var "x"), Var "w"));;
let m4 = (App (App (Lam ("z",Var "z"), Lam ("x", Var "x")), Var "w"))

let m1_zforx = subst m1 "x" (Var "z");;
let m1_m2fory = subst m1 "y" m2
let m2_ughforz = subst m2 "z" (Var "ugh")
let m3_zforx = subst m3 "x" (Var "z")
let m1_m3fory = subst m1 "y" m3

let m2red = reduce m2
let m3red = reduce m3
let m4red1 = reduce m4
let m4red2 = reduce m4red1
let m13sred = reduce m1_m3fory

print_lambda m1; print_newline ();;
print_lambda m2; print_newline ();;

let is_there_a_2 = App(App(find, (num 2)), my_list)
let is_there_a_3 = App(App(find, (num 3)), my_list)
let is_there_a_4 = App(App(find,(num 4)), my_list)
let is_there_a_5 = App(App(find, (num 5)), my_list)

let should_be_empty_list = bigstep_reduce is_there_a_2
let should_be_one = bigstep_reduce is_there_a_3
let should_be_empty_list = bigstep_reduce is_there_a_4
let should_be_empty_list = bigstep_reduce (App(App(find, (num 2)), empty))
let should_be_two = bigstep_reduce is_there_a_5

let is_5_with_count = bigstep_reduce_with_count is_there_a_5 (*see that reductions are 315*)

*)