type expr =
  | Var of string
  | Not of expr
  | And of expr * expr
  | Or of expr * expr

type bdd =
  | Leaf of bool
  | Node of string * hashconsed * hashconsed

and hashconsed = Hc of bdd [@@hashconsed]

let leaf x = Hc (Leaf x)
let node (v, l, r) = Hc (Node (v, l, r))

(* Pretty print a BDD *)
let rec print_bdd indent bdd' =
  match bdd' with Hc bdd ->
    match bdd with
  | Leaf b ->
      print_endline (indent ^ (if b then "1" else "0"))
  | Node (var, low, high) ->
      print_endline (indent ^ var ^ " ?");
      print_bdd (indent ^ "  | ") low;
      print_endline (indent ^ " :");
      print_bdd (indent ^ "  | ") high

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

let and_bdd_memo = 
  let rec and_bdd self (h, h') =
    match (h, h') with Hc z, Hc z' ->
    if z = Leaf false || z' = Leaf false then
      leaf false
    else if z = Leaf true then
      h'
    else if z' = Leaf true then
      h
    else if z = z' then h
    else
      match (z, z') with
      | (Node (p, x, y), Node (p', x', y')) ->
          if p = p' then node (p, self (x, x'), self (y, y'))
          else if p < p' then node (p, self (x, h') , self (y, h'))
          else node (p', self (h, x'), self (h, y'))
      | _ -> assert false
  in memo_rec and_bdd

let or_bdd_memo = 
  let rec or_bdd self (h, h') =
    match (h, h') with Hc z, Hc z' ->
    if z = Leaf true || z' = Leaf true then
    leaf true
    else if z = Leaf false then
      h'
    else if z' = Leaf false then
      h
    else if z = z' then h
    else
      match (z, z') with
      | (Node (p, x, y), Node (p', x', y')) ->
          if p = p' then node (p, self (x, x'), self (y, y'))
          else if p < p' then node (p, self (x, h') , self (y, h'))
          else node (p', self (h, x'), self (h, y'))
      | _ -> assert false
  in memo_rec or_bdd

(* Convert a propositional formula to a BDD *)
let formula_to_bdd_memo = 
let rec formula_to_bdd self formula =
  Gc.minor();
  match formula with
  | Var name ->
      node (name, leaf false, leaf true)
  | Not a ->
      let rec negate_bdd bdd' =
        match bdd' with Hc bdd ->
        match bdd with
        | Leaf b -> leaf (not b)
        | Node (v, l, r) -> node (v, negate_bdd l, negate_bdd r)
      in
      let a' = self a in
      negate_bdd a'
  | And (a, a') ->
      let h = self a in
      let h' = self a' in
      if h = h' then h else
      (match (h, h') with Hc z, Hc z' ->
        if z = Leaf false || z' = Leaf false then
          leaf false
        else if z = Leaf true then
          h'
        else if z' = Leaf true then
          h
        else
      (match (z, z') with
      | (Node (p, x, y), Node (p', x', y')) ->
          if p = p' then node (p, and_bdd_memo (x, x'), and_bdd_memo (y, y'))
          else if p < p' then node (p, and_bdd_memo (x, h'), and_bdd_memo (y, h'))
          else node (p', and_bdd_memo (h, x'), and_bdd_memo (h, y'))
          | _ -> assert false))
  | Or (a, a') ->
      let h = self a in
      let h' = self a' in
      if h = h' then h else
      match (h, h') with Hc z, Hc z' ->
        if z = Leaf true || z' = Leaf true then
          leaf true
        else if z = Leaf false then
          h'
        else if z' = Leaf false then
          h
        else
      match (z, z') with
      | (Node (p, x, y), Node (p', x', y')) ->
          if p = p' then node (p, or_bdd_memo (x, x'), or_bdd_memo (y, y'))
          else if p < p' then node (p, or_bdd_memo (x, h'), or_bdd_memo (y, h'))
          else node (p', or_bdd_memo (h, x'), or_bdd_memo (h, y'))
          | _ -> assert false
in memo_rec formula_to_bdd


let every_pigeon_in_a_hole n = 
  let result = ref None in
  for p = 1 to (n+1) do 
    let term = ref None in
    for h = 1 to n do 
      let new_term = match !term with
                      | None -> Some (Var ("x" ^ string_of_int p ^ string_of_int h))
                      | Some t -> Some (Or (Var ("x" ^ string_of_int p ^ string_of_int h), t))
                    in
    term := new_term
    done;
    match !term with
    | None -> assert false
    | Some t -> let new_result = match !result with
                                  | None -> Some t
                                  | Some r -> Some (And (r, t))
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
                            | None -> Some (Or (Not (Var ("x" ^ string_of_int p ^ string_of_int h)),Not( Var ("x" ^ string_of_int q ^ string_of_int h))))
                            | Some s -> Some (And (Or (Not (Var ("x" ^ string_of_int p ^ string_of_int h)),Not( Var ("x" ^ string_of_int q ^ string_of_int h))), s))
                          in
          second := new_second
      done;
      match !second with
      | None -> assert false
      | Some s -> let new_first = match !first with
                                  | None -> Some s
                                  | Some f -> Some (And (f, s))
                  in
      first := new_first
    done;
    match !first with
    | None -> assert false
    | Some f -> let new_result = match !result with
                                  | None -> Some f
                                  | Some r -> Some (And (r, f))
                in
    result := new_result
  done;
  match !result with
  | None -> assert false
  | Some r -> r

let pigeonhole n = And (every_pigeon_in_a_hole n, no_two_pigeons_in_same_hole n)
(* Test the BDD conversion *)
let formula = pigeonhole 10
let bdd = formula_to_bdd_memo formula
let () = Gc.full_major() 
let () = Gc.print_stat(stdout)