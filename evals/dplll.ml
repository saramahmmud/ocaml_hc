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
  | [c] ->  print_string "(" ; print_disj c ; print_string ")"
  | c :: rest -> print_string "(" ; print_disj c ; print_string ") ∧ " ; print_cnf rest

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
      | ATOM(x)              -> atom(x)
      | NOT(e)               -> not_(self(e))
      | AND(e1, e2)          -> and_(self(e1), self(e2))
      | OR(e1, e2)           -> or_(self(e1), self(e2))
      | TRUE                 -> true_
      | FALSE                -> false_
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

let distr =
  let rec distr_memo self (e1', e2') =
  match e1', e2' with Hc e1, Hc e2 -> match e1, e2 with
    | AND(e1, e2), _ -> and_(self (e1, e2'), self (e2, e2'))
    | _, AND(e1, e2) -> and_(self (e1', e1), self (e2', e2))
    | _, _ -> or_(e1', e2')
  in memo_rec distr_memo 

(*push disjunctions in until they only apply to literals (NOT or ATOM)*)
let dis = 
  let rec dis_memo self x =
  match x with Hc x' -> match x' with
    | OR(e1, e2) -> let e1' = self(e1) and e2' = self(e2) in distr (e1', e2')
    | AND(e1, e2)          -> and_(self(e1), self(e2))
    | _ -> x 
  in memo_rec dis_memo 

let cnf e = dis(neg(impl(e)))

(*convert cnf to list of lists of disjunctions*)
let rec to_clauses x = 
  match x with Hc x' -> match x' with
    | AND(e1, e2)          -> to_clauses(e1) @ to_clauses(e2)
    | OR (e1, e2) -> let l1 = match to_clauses e1 with
                                | [x] -> x
                                | _ -> assert false
                              in
                     let l2 = match to_clauses e2 with
                                | [x] -> x
                                | _ -> assert false 
                              in 
                      [l1 @ l2]
    | ATOM(_)| NOT(_) | TRUE| FALSE -> [[x]]
    | _ -> assert false

let rec is_in x = function
| []                   -> false
| h :: t               -> if h = x then true else is_in x t

let rec remove x = function
| []                   -> []
| h :: t               -> if h = x then remove x t else h :: remove x t

(*check if a list of disjuntions contains a literal and its negation*)
let rec is_taut disj =
  match disj with
    | [] -> true
    | [x] -> if x = true_ then true else false
    | x::xs -> if (is_in (neg (not_ x)) xs) || (is_in true_ xs) then true else is_taut xs

(*remove tautologies*)
let rec remove_tautologies clauses =
  match clauses with
    | [] -> []
    | x::xs -> if is_taut x then remove_tautologies xs else x::remove_tautologies xs



(*unit propogation*)
let rec unit_propogate clauses = 
  match clauses with
  | [] -> []
  | x::xs -> let rec get_first_unit clauses =
              match clauses with
              | [] -> None
              | x::xs -> if List.length x = 1 then
                            let l = match x with
                                      | [x] -> x
                                      | _ -> assert false
                                    in
                            Some l
                          else get_first_unit xs
                        in
              let unit_clause = get_first_unit clauses in
              match unit_clause with 
              | None -> clauses
              | Some u -> 
                let rec delete_containing_unit clauses unit_clause = 
                  match clauses with 
                  | [] -> []
                  | x::xs -> if is_in unit_clause x then delete_containing_unit xs unit_clause else x::delete_containing_unit xs unit_clause
                in let clauses = delete_containing_unit clauses u in
                let rec delete_negated_unit clauses unit_clause = 
                  match clauses with 
                  | [] -> []
                  | x::xs -> 
                    let negated = (neg (not_ unit_clause)) in
                    (remove negated x)::delete_negated_unit xs unit_clause
                  in let clauses = delete_negated_unit clauses u in
                  unit_propogate clauses

(*pure literal elimination*)
let rec pure_literal_elimination clauses=
  match clauses with
  | [] -> []
  | x::xs -> (*convert list of lists to a set*)
              let rec flatten clauses = 
                (match clauses with
                | [] -> []
                | x::xs -> x @ flatten xs)
              in 
              let flat = flatten clauses in
              let rec get_first_pure list = 
                (match list with
                | [] -> None
                | x::xs -> if is_in (neg (not_ x)) flat then get_first_pure xs else Some x)
              in
              let pure = get_first_pure flat in
              match pure with
              | None -> clauses
              | Some p -> 
                let rec delete_containing clauses pure = 
                  match clauses with 
                  | [] -> []
                  | x::xs -> if is_in pure x then delete_containing xs pure else x::delete_containing xs pure
                in let clauses = delete_containing clauses p in
                pure_literal_elimination clauses

(*no clauses = negation is satisfiable, so original was not. 
  empty clause= negation is unsatisfiable, so original was*)
let rec dpll_alg clauses = 
  match clauses with 
  | [] -> false
  | x::xs ->  if is_in [] clauses then true else
              let c = remove_tautologies clauses in
              let c = unit_propogate c in
              let c = pure_literal_elimination c in
              if c <> clauses then dpll_alg c else
                let rec get_first_literal clauses =
                  match clauses with
                  | [] -> None
                  | x::xs -> if List.length x > 0 then
                                let l = match x with
                                          | y::ys -> y
                                          | _ -> assert false
                                        in
                                Some l
                              else get_first_literal xs
                            in
                let literal = get_first_literal clauses in
                match literal with
                | None -> false
                | Some l -> 
                  let rec delete_containing_literal clauses literal = 
                    match clauses with 
                    | [] -> []
                    | x::xs -> if is_in literal x then delete_containing_literal xs literal else x::delete_containing_literal xs literal
                  in 
                  let rec remove_negated_literal clauses literal = 
                    match clauses with 
                    | [] -> []
                    | x::xs -> 
                      let negated = (neg (not_ literal)) in
                      (remove negated x)::remove_negated_literal xs literal
                  in let clauses_l = (delete_containing_literal (remove_negated_literal clauses l) l) 
                  in let clauses_not_l = (delete_containing_literal (remove_negated_literal clauses (neg (not_ l))) (neg (not_ l)))
                in dpll_alg clauses_l || dpll_alg clauses_not_l

let dpll expr = 
  let clauses = to_clauses (cnf (not_ expr)) in
  dpll_alg clauses

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

let test = pigeon 3
let _ = Gc.minor()
let _ = print_cnf (to_clauses (cnf test)); print_endline ""
let _ = Gc.full_major(); Gc.print_stat stdout