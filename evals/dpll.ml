(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*                             Sara Mahmmud                               *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)

type expr =
    | ATOM of string
    | NOT of hashconsed
    | AND of hashconsed * hashconsed
    | OR of hashconsed * hashconsed
    | IMPLIES of hashconsed * hashconsed
    | BIIMPLIES of hashconsed * hashconsed
    | TRUE
    | FALSE

and hashconsed = Hc of expr [@@hashconsed]

let atom a = Hc (ATOM a)
let not_ e = Hc (NOT e)
let and_ (e1, e2) = Hc (AND (e1, e2))
let or_ (e1, e2) = Hc (OR (e1, e2))
let implies (e1, e2) = Hc (IMPLIES (e1, e2))
let biimplies (e1, e2) = Hc (BIIMPLIES (e1, e2))
let true_ = Hc TRUE
let false_ = Hc FALSE

let rec print_expr expr' =
  match expr' with Hc expr ->
    match expr with
  | ATOM c -> print_string c
  | NOT e -> print_string "¬"; print_expr e
  | AND (e1, e2) -> print_string "("; print_expr e1; print_string " ∧ "; print_expr e2; print_string ")"
  | OR (e1, e2) -> print_string "("; print_expr e1; print_string " ∨ "; print_expr e2; print_string ")"
  | IMPLIES (e1, e2) -> print_string "("; print_expr e1; print_string " → "; print_expr e2; print_string ")"
  | BIIMPLIES (e1, e2) -> print_string "("; print_expr e1; print_string " ↔ "; print_expr e2; print_string ")"
  | TRUE -> print_string "⊤"
  | FALSE -> print_string "⊥"

(*pretty print list of lists of clauses*)
let rec print_cnf cnf =
  match cnf with
  | [] -> print_string "no clauses"
  | [c] ->  print_string "[" ; print_disj c ; print_string "]"
  | c :: rest -> print_string "[" ; print_disj c ; print_string "] ∧ " ; print_cnf rest

and print_disj conj =
  match conj with
  | [] -> print_string "empty clause"
  | [d] -> print_expr d
  | d :: rest -> print_expr d ; print_string " v " ; print_disj rest

let memo_rec f =
  let h = Hashtbl.create 2550 in
  let rec g x =
    try Hashtbl.find h x
    with Not_found ->
      let y = f g x in
      Hashtbl.add h x y;
      y
  in
  g

(*eliminate implications and biimplications*)
let impl = 
  let rec impl_memo self x = 
  match x with Hc x' -> match x' with
      | IMPLIES(e1, e2)      -> or_(not_(self(e1)), self(e2))
      | BIIMPLIES(e1, e2)    -> and_(self(implies(e1, e2)), self(implies(e2, e1)))
      | NOT(e)               -> not_(self(e))
      | AND(e1, e2)          -> and_(self(e1), self(e2))
      | OR(e1, e2)           -> or_(self(e1), self(e2))
      | _ -> x
  in memo_rec impl_memo

(*push negations in until they only apply to literals*)
let neg = 
  let rec neg_memo self x =
  match x with Hc x' -> match x' with
    | NOT(Hc AND(e1, e2))     -> or_(self(not_(e1)), self(not_(e2)))
    | NOT(Hc OR(e1, e2))      -> and_(self(not_(e1)), self(not_(e2)))
    | NOT(Hc NOT(e))          -> self(e)
    | NOT(Hc TRUE)          -> false_
    | NOT(Hc FALSE)          -> true_
    | AND(e1, e2)          -> and_(self(e1), self(e2))
    | OR(e1, e2)           -> or_(self(e1), self(e2))
    | _ -> x
  in memo_rec neg_memo

let new_var = 
  let counter = ref 0 in
  fun () -> counter := !counter +1; atom ("t" ^ string_of_int !counter)

let set_union x y =
  let rec aux acc = function
    | [] -> acc
    | x :: xs -> if List.mem x acc then aux acc xs else aux (x :: acc) xs
  in aux y x

let apply_to_all f clauses = 
  List.map (List.map f) clauses

let double_not d = 
  match d with
    | Hc (NOT (Hc (NOT e))) -> e
    | _ -> d

let rec tseitin_rec nnf' = 
  match nnf' with Hc nnf ->
    match nnf with
    | AND (e1, e2) -> (match tseitin_rec e1, tseitin_rec e2 with
                      | (t1, c1), (t2, c2) -> 
                        let t = new_var() in
                        let c3 = [[not_(t); t1]; [not_(t); t2]; [t; not_(t1); not_(t2)]] in
                        let c3 = apply_to_all double_not c3 in
                        let clauses = set_union c1 (set_union c2 c3) in
                        (t, clauses))
    | OR (e1, e2) -> (match tseitin_rec e1, tseitin_rec e2 with
                      | (t1, c1), (t2, c2) -> 
                        let t = new_var() in
                        let c3 = [[not_(t); t1; t2]; [t; not_(t1)]; [t; not_(t2)]] in
                        let c3 = apply_to_all double_not c3 in
                        let clauses = set_union c1 (set_union c2 c3) in
                        (t, clauses))
    | ATOM e | NOT (Hc (ATOM e)) -> (nnf', [])
    | _ -> assert false

let tseitin nnf' = 
  match nnf' with Hc nnf ->
    match nnf with 
    | TRUE -> []
    | FALSE -> [[]]
    | _ -> let n = tseitin_rec nnf' in
            match n with
            | (t, clauses) -> [t] :: clauses

let cnf e = tseitin(neg(impl(e)))

let rec remove x = function
| []                   -> []
| h :: t               -> if h = x then remove x t else h :: remove x t

(*check if a list of disjuntions contains a literal and its negation*)
let rec is_taut disj =
  match disj with
    | [] -> true
    | [x] -> if x = true_ then true else false
    | x::xs -> if (List.mem (neg (not_ x)) xs) || (List.mem true_ xs) then true else is_taut xs

(*remove tautologies*)
let rec remove_tautologies clauses =
  match clauses with
    | [] -> []
    | x::xs -> if is_taut x then remove_tautologies xs else x::remove_tautologies xs

(*unit propogation*)
let rec unit_propogate l clauses = 
  let rec delete_containing_unit c = 
    match c with 
    | [] -> []
    | x::xs -> if List.mem l x then delete_containing_unit xs  
        else x::delete_containing_unit xs 
  in let clauses = delete_containing_unit clauses in
  let negated = (neg (not_ l)) in
  let rec delete_negated_unit c = 
    match c with 
    | [] -> []
    | x::xs -> (remove negated x)::delete_negated_unit xs 
  in delete_negated_unit clauses

(*pure literal elimination*)
let rec pure_literal_elimination l c =
  let rec delete_containing clauses literal = 
    match clauses with 
    | [] -> []
    | x::xs -> if List.mem literal x then delete_containing xs literal else x::delete_containing xs literal
  in delete_containing c l

let rec contains_unit clauses =
  match clauses with
  | [] -> false, []
  | x::xs -> if List.length x = 1 then (true , x) else contains_unit xs

let rec contains_pure clauses = 
  let rec setify clauses acc = 
    match clauses with
    | [] -> []
    | x::xs -> setify xs (set_union x acc)
  in 
  let literals = setify clauses [] in
  let rec get_first_pure set = 
    (match set with
    | [] -> false, false_
    | x::xs -> if List.mem (neg (not_ x)) literals then get_first_pure xs else (true, x))
  in get_first_pure literals

let rec choose_first_literal clauses =
  match clauses with
  | [] -> assert false
  | x::xs -> match x with
    | y::ys -> y
    | _ -> assert false
                      
let rec dpll_rec clauses = 
  match contains_unit clauses with
  | true , [x] -> dpll_rec (unit_propogate x clauses)
  | _ -> match contains_pure clauses with
    | true, x -> dpll_rec (pure_literal_elimination x clauses)
    | _ -> match clauses with
      | [] -> false
      | _ -> if List.mem [] clauses then true else
        let case = choose_first_literal clauses in
        (dpll_rec ([case]::clauses)) || (dpll_rec ([neg (not_ case)]::clauses))

let dpll expr = 
  let clauses = (cnf (not_ expr)) in
  dpll_rec clauses

let every_pigeon_in_a_hole n = 
  let result = ref None in
  for p = 1 to (n+1) do 
    let term = ref None in
    for h = 1 to n do 
      let new_term = match !term with
                      | None -> Some (atom ("x" ^ string_of_int p ^ string_of_int h))
                      | Some t -> Some (or_ (atom ("x" ^ string_of_int p ^ string_of_int h), t))
                    in
    term := new_term
    done;
    match !term with
    | None -> assert false
    | Some t -> let new_result = match !result with
                                  | None -> Some t
                                  | Some r -> Some (and_ (r, t))
                in
  result := new_result
  done;
  match !result with
  | None -> assert false
  | Some r -> r

let no_two_pigeons_in_same_hole n = 
  let result = ref None in
  for h = 1 to n do 
    let first = ref None in
    for p = 1 to (n+1) do 
      let second = ref None in
      for q = 1 to (n+1) do 
        if p <> q then 
          let new_second = match !second with
                            | None -> Some (or_ (not_ (atom ("x" ^ string_of_int p ^ string_of_int h)),not_( atom ("x" ^ string_of_int q ^ string_of_int h))))
                            | Some s -> Some (and_ (or_ (not_ (atom ("x" ^ string_of_int p ^ string_of_int h)),not_( atom ("x" ^ string_of_int q ^ string_of_int h))), s))
                          in
          second := new_second
      done;
      match !second with
      | None -> assert false
      | Some s -> let new_first = match !first with
                                  | None -> Some s
                                  | Some f -> Some (and_ (f, s))
                  in
      first := new_first
    done;
    match !first with
    | None -> assert false
    | Some f -> let new_result = match !result with
                                  | None -> Some f
                                  | Some r -> Some (and_ (r, f))
                in
    result := new_result
  done;
  match !result with
  | None -> assert false
  | Some r -> r

  let two_pigeons_in_same_hole n = 
    let result = ref None in
    for h = 1 to n do 
      let first = ref None in
      for p = 1 to (n+1) do 
        let second = ref None in
        for q = 1 to (n+1) do 
          if p <> q then 
            let new_second = match !second with
                              | None -> Some (and_ (atom ("x" ^ string_of_int p ^ string_of_int h), atom ("x" ^ string_of_int q ^ string_of_int h)))
                              | Some s -> Some (or_ (and_ (atom ("x" ^ string_of_int p ^ string_of_int h), atom ("x" ^ string_of_int q ^ string_of_int h)), s))
                            in
            second := new_second
        done;
        match !second with
        | None -> assert false
        | Some s -> let new_first = match !first with
                                    | None -> Some s
                                    | Some f -> Some (or_ (f, s))
                    in
        first := new_first
      done;
      match !first with
      | None -> assert false
      | Some f -> let new_result = match !result with
                                    | None -> Some f
                                    | Some r -> Some (or_ (r, f))
                  in
      result := new_result
    done;
    match !result with
    | None -> assert false
    | Some r -> r

let pigeon n = implies (every_pigeon_in_a_hole n, two_pigeons_in_same_hole n)

let test = pigeon 6
let _ = print_endline (string_of_bool (dpll test))
let _ = Gc.full_major(); Gc.print_stat stdout