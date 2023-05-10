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
  let h = Hashtbl.create 255 in
  let rec g x =
    try Hashtbl.find h x
    with Not_found ->
      let y = f g x in
      Hashtbl.add h x y;
      y
  in
  g

let rec and_bdd h h' =
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
        if p = p' then node (p, and_bdd x x', and_bdd y y')
        else if p < p' then node (p, and_bdd x h' , and_bdd y h')
        else node (p', and_bdd h x', and_bdd h y')
    | _ -> assert false

let rec or_bdd h h' =
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
        if p = p' then node (p, or_bdd x x', or_bdd y y')
        else if p < p' then node (p, or_bdd x h' , or_bdd y h')
        else node (p', or_bdd h x', or_bdd h y')
    | _ -> assert false

(* Convert a propositional formula to a BDD *)
let rec formula_to_bdd formula =
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
      let a' = formula_to_bdd a in
      negate_bdd a'
  | And (a, a') ->
      let h = formula_to_bdd a in
      let h' = formula_to_bdd a' in
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
          if p = p' then node (p, and_bdd x x', and_bdd y y')
          else if p < p' then node (p, and_bdd x h', and_bdd y h')
          else node (p', and_bdd h x', and_bdd h y')
          | _ -> assert false))
  | Or (a, a') ->
      let h = formula_to_bdd a in
      let h' = formula_to_bdd a' in
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
          if p = p' then node (p, or_bdd x x', or_bdd y y')
          else if p < p' then node (p, or_bdd x h', or_bdd y h')
          else node (p', or_bdd h x', or_bdd h y')
          | _ -> assert false


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

(* Test the BDD conversion *)
let formula = And (every_pigeon_in_a_hole 7, no_two_pigeons_in_same_hole 7)
let bdd = formula_to_bdd formula
let () = Gc.full_major() 
let () = Gc.print_stat(stdout)