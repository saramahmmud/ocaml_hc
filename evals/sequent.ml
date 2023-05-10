(*A sequent calculus prover for propositional logic*)

type prop =
  | Atom of string
  | Not of hashconsed
  | And of hashconsed * hashconsed
  | Or of hashconsed * hashconsed
  | Imp of hashconsed * hashconsed
and hashconsed = Hc of prop [@@hashconsed]

type sequent = Sequent of hashconsed list * hashconsed list

exception Fail of string

let atom x = Hc (Atom x)
let not_ x = Hc (Not x)
let and_ (x, y) = Hc (And (x, y))
let or_ (x, y) = Hc (Or (x, y))
let imp (x, y) = Hc (Imp (x, y))

let rec list_without l w = 
  match l with
  | [] -> []
  | h::t -> if h = w then t else h::(list_without t w)

let remove_duplicates l = 
  let rec remove_duplicates_helper l acc =
    match l with
    | [] -> acc
    | h::t -> if List.mem h acc then remove_duplicates_helper t acc else remove_duplicates_helper t (h::acc)
  in
  remove_duplicates_helper l []

let not_l (assumptions, goals) prop =
  let new_assumptions = list_without assumptions prop in
  let new_goals = remove_duplicates (prop :: goals) in
  Sequent (new_assumptions, new_goals)

let not_r (assumptions, goals) prop =
  let new_goals = list_without goals prop in
  let new_assumptions = remove_duplicates (prop :: assumptions) in
  Sequent (new_assumptions, new_goals)

let and_l (assumptions, goals) prop=
  match prop with 
  | Hc (And (x, y)) -> 
    let assumptions_to_add = [x; y] in
    let new_assumptions' = list_without assumptions prop in
    let new_assumptions = remove_duplicates (assumptions_to_add @ new_assumptions') in
    Sequent (new_assumptions, goals)
  | _ -> raise (Fail "and_l")

let and_r (assumptions, goals) prop =
  match prop with
    | Hc (And (x, y)) -> 
      let other_goals = list_without goals prop in
      let new_goals_l = remove_duplicates (x :: other_goals) in
      let new_goals_r = remove_duplicates (y :: other_goals) in
      Sequent (assumptions, new_goals_l), Sequent (assumptions, new_goals_r)
    | _ -> raise (Fail "and_r")

let or_l (assumptions, goals) prop =
  match prop with
    | Hc (Or (x, y)) -> 
      let other_assumps = list_without assumptions prop in
      let new_assumps_l = remove_duplicates (x :: other_assumps) in
      let new_assumps_r = remove_duplicates (y :: other_assumps) in
      Sequent (new_assumps_l, goals), Sequent (new_assumps_r, goals)
    | _ -> raise (Fail "or_l")

let or_r (assumptions, goals) prop =
  match prop with 
  | Hc (Or (x, y)) -> 
    let goals_to_add = [x; y] in
  let new_goals' = list_without goals prop in
  let new_goals = remove_duplicates (goals_to_add @ new_goals') in
  Sequent (assumptions, new_goals)
  | _ -> raise (Fail "or_r")

let imp_l (assumptions, goals) prop =
  match prop with  
    | Hc (Imp (x, y)) -> 
      let other_assumps = list_without assumptions prop in
      let new_goals_l = remove_duplicates (x :: goals) in
      let new_assumps_r = remove_duplicates (y :: other_assumps) in
      Sequent (assumptions, new_goals_l), Sequent (new_assumps_r, goals)
    | _ -> raise (Fail "imp_l")

let imp_r (assumptions, goals) prop =
  match prop with
    | Hc (Imp (x, y)) ->
      let other_goals = list_without goals prop in
      let new_assumps_l = remove_duplicates (x :: assumptions) in
      let new_goals_r = remove_duplicates (y :: other_goals) in
      Sequent (new_assumps_l, new_goals_r)
    | _ -> raise (Fail "imp_r")

let rec next_non_atom l = 
  match l with
  | [] -> raise (Fail "next_non_atom")
  | h::t -> match h with
    | Hc (Atom x) -> next_non_atom t
    | _ -> h

let rec all_atoms l = 
  match l with
  | [] -> true
  | h::t -> match h with
    | Hc (Atom x) -> all_atoms t
    | _ -> false

let rec is_basic a' g' =
  match a' with
  | [] -> false
  | x :: xs -> List.exists (fun i -> i = x) g' || is_basic xs g'

let prove_sequent (Sequent (a, g)) = 
  let rec prove_rec (Sequent (assumptions, goals)) = 
    if (all_atoms assumptions) && (all_atoms goals) then is_basic assumptions goals
    else if (all_atoms assumptions) then
        (let next = next_non_atom goals in
        match next with
        | Hc (Not x) -> prove_rec (not_r (assumptions, goals) next)
        | Hc (And (x, y)) -> (match (and_r (assumptions, goals) next) with
          | (Sequent (a1, g1), Sequent (a2, g2)) -> prove_rec (Sequent (a1, g1)) && prove_rec (Sequent (a2, g2)))
        | Hc (Or (x, y)) -> prove_rec (or_r (assumptions, goals) next)
        | Hc (Imp (x, y)) -> prove_rec (imp_r (assumptions, goals) next)
        | _ -> raise( Fail "prove_rec"))
    else if (all_atoms goals) then
        (let next = next_non_atom assumptions in
        match next with
        | Hc (Not x) -> prove_rec (not_l (assumptions, goals) next)
        | Hc (And (x, y)) -> prove_rec (and_l (assumptions, goals) next)
        | Hc (Or (x, y)) -> (match (or_l (assumptions, goals) next) with
          | (Sequent (a1, g1), Sequent (a2, g2)) -> prove_rec (Sequent (a1, g1)) && prove_rec (Sequent (a2, g2)))
        | Hc (Imp (x, y)) -> (match (imp_l (assumptions, goals) next) with
          | (Sequent (a1, g1), Sequent (a2, g2)) -> prove_rec (Sequent (a1, g1)) && prove_rec (Sequent (a2, g2)))
        | _ -> raise (Fail "prove_rec"))
    else raise (Fail "prove_rec")
  in
  prove_rec (Sequent (a, g))

let prove prop = prove_sequent (Sequent ([], [prop]))

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

(* Test the BDD conversion *)
let pigeon n = and_ (every_pigeon_in_a_hole n, no_two_pigeons_in_same_hole n)

let formula = pigeon 70

let _ = Printf.printf "%b\n" (prove formula)
let _ = Gc.full_major(); Gc.print_stat(stdout)
