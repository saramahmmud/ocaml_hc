(*Lambda calculus with de bruijn indices*)

(*Terms*)
type term = 
  | Var of int          (*De Bruijn indices, starting from 0*)
  | Lam of term         (*Lambda abstraction*)
  | App of term * term  (*Application*)      

(*Shift the index of free variables, with index>cutoff, by d*)
let rec shift d cutoff term = 
  match term with
  | Var k -> if k>= cutoff then Var (k + d) else Var k
  | Lam t -> Lam (shift d (cutoff + 1) t)
  | App (t1, t2) -> App (shift d cutoff t1, shift d cutoff t2)

(*Substitution of s for j in term*)
let rec subst s j term = 
  match term with
  | Var k -> if k=j then s else Var k
  | Lam t -> Lam (subst (shift 1 0 s) (j + 1) t)
  | App (t1, t2) -> App (subst s j t1, subst s j t2)

(*Beta reduction*)
let rec reduce term =
  match term with
  | App (Lam t1, t2) -> shift (-1) 0 (subst (shift 1 0 t2) 0 t1)
  | App (e1, e2) ->
    let e1' = reduce e1 in
    if e1' <> e1 then App(e1', e2)
    else 
      let e2' = reduce e2 in App(e1, e2')
  | Lam (e) -> Lam (reduce e) (* reduce under the lambda (!) *)
  | term -> term

let bigstep_reduce_with_count e =
  let rec helper e count =
    let e' = reduce e in
    if e' = e then (e, count)
    else helper e' (count+1)
  in helper e 0

(*Pretty printing*)
let rec print_term term = 
  match term with
  | Var k -> print_int k;
  | Lam t -> print_string "(\\"; print_term t; print_string ")"
  | App (t1, t2) -> print_string "("; print_term t1; print_string " "; print_term t2; print_string ")"

let num n = 
  let rec helper n =
    if n= 0 then Var 0
    else
      App(Var 1, (helper (n-1)))
    in Lam(Lam(helper n));;
  
(*Y*)
let y = Lam(App(Lam(App(Var 1, App(Var 0, Var 0))), Lam(App(Var 1, App(Var 0, Var 0)))))

(*id*)
let id = Lam(Var 0)

(*booleans*)
let t = Lam(Lam(Var 1))
let f = Lam(Lam(Var 0))
let logical_not = Lam(App(App(Var 0, f), t))
let logical_and = Lam(Lam(App(App(Var 1, Var 0), f)))

(*arithmetic*)
let zero = num 0
let succ = Lam(Lam(Lam(App(Var 1, App(App(Var 2, Var 1), Var 0)))))
let pred = Lam(Lam(Lam(App(App(App(Var 2, Lam(Lam(App(Var 0, App(Var 1, Var 3))))), Lam(Var 1)), Lam(Var 0)))))
let subtract = Lam(Lam(App(App(Var 0, pred), Var 1)))

(*predicates*)
let isZero = Lam(App(App(Var 0, Lam(f)), t))
let leq = Lam(Lam(App(isZero, App(App(subtract, Var 1), Var 0))))
let gre = Lam(Lam(App(logical_not, App(App(leq, Var 1), Var 0))))
let eq = Lam(Lam(App(App(logical_and, App(App(leq, Var 1), Var 0)), App(App(leq, Var 0), Var 1))))


(*Pairs*)
let pair = Lam(Lam(Lam (App(App(Var 0, Var 2), Var 1))))
let first = Lam(App(Var 0, Lam(Lam(Var 1))))
let second = Lam(App(Var 0, Lam(Lam(Var 0))))


(*Lists*)
let empty = Lam(Lam(Var 1))
let cons = Lam(Lam(Lam(Lam(App(App(Var 0, Var 3), Var 2)))))
let head = Lam(App(App(Var 0, f), t))
let tail = Lam(App(App(Var 0, f), f))
let isEmpty = Lam(App(App(Var 0, t), Lam(Lam(f))))

let flip = Lam(Lam(Lam(App(App(Var 2, Var 0), Var 1))))

let rec list_builder = function
  | [] -> empty
  | h::t -> App(App(cons, (num h)), (list_builder t))

(*Return the index of the item in the list if it exists else empty list*)
let fFind = Lam(Lam(Lam(Lam(App(App(App(isEmpty, Var 1), empty), App(App(App(App(eq, Var 2), App(head, Var 0)), Var 0), App(App(App(Var 3, Var 2), App(tail, Var 1)), App(succ, Var 0))))))))
let find = Lam(Lam(App(App(App(App(y, fFind), Var 1), Var 0), zero)))

(*Get list element at index i*)
let fGet = Lam(Lam(Lam(Lam(App(App(App(isEmpty, Var 1), empty), App(App(App(App(eq, Var 2), Var 0), App(head, Var 1)), App(App(App(Var 3, Var 2), App(tail, Var 1)), App(succ, Var 0))))))))
let get = Lam(Lam(App(App(App(App(y, fGet), Var 1), Var 0), zero)))

(*Merge lists x and y*)
let fMerge = Lam(Lam(Lam(App(App(Var 1, Var 0), Lam(Lam(App(App(cons, Var 1), App(App(Var 4, Var 0), Var 2))))))))
let merge = App(y, fMerge)

(*Reverse list l*)
let fReverse = Lam(Lam(Lam(App(App(App(isEmpty, Var 1), Var 0), App(App(Var 2, App(tail, Var 1)), App(App(cons, App(head, Var 1)), Var 0))))))
let reverse = Lam(App(App(App(y, fReverse), Var 0), empty))

(*Remove elements of list l that satisfy condition p*)
let fRemove = Lam(Lam(Lam(App(App(Var 0, empty), Lam(Lam(App(App(App(App(Var 3, Var 1), id), App(cons, Var 1)), App(App(Var 4, Var 3), Var 0))))))))
let remove = App(y, fRemove)

(*quick sort a list l of Church numerals in ascending order*)
let fQuickSort = Lam(Lam(App(App(Var 0, empty), Lam(Lam(App(App(merge, App(Var 3, App(App(remove, App(App(flip, gre), Var 1)), Var 0))), App(App(cons, Var 1), App(Var 3, App(App(remove, App(App(flip, leq), Var 1)), Var 0)))))))))
let quickSort = App(y, fQuickSort)


let my_list = match bigstep_reduce_with_count (list_builder  [9; 1; 4; 2; 7; 6]) with | (x, _) -> x
let _ = print_term my_list; print_endline ""
let sort_with_count = match bigstep_reduce_with_count (App(quickSort, my_list)) with | (x, _) -> x
let _ = print_term sort_with_count; print_endline ""

