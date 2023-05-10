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

(*Lambda calculus with de bruijn indices*)

(*Terms*)
type term = 
  | Var of int          (*De Bruijn indices, starting from 0*)
  | Lam of hashconsed         (*Lambda abstraction*)
  | App of hashconsed * hashconsed  (*Application*)      

and hashconsed = Hc of term [@@hashconsed]

let app (x1, x2) = Hc (App (x1, x2))
let lam x = Hc (Lam x)
let var x = Hc (Var x)

(*Shift the index of the free variables in term t, with index>cutoff c, by d*)
let rec shift d c t = 
  match t with
  | Hc t' -> 
    (match t' with
    | Var k -> if k>= c then var (k + d) else var k
    | Lam t'' -> lam (shift d (c + 1) t'')
    | App (t1, t2) -> app (shift d c t1, shift d c t2))

(*Substitution of s for j in term*)
let rec subst s j t = 
  match t with
  | Hc t'->
    (match t' with
    | Var k -> if k=j then s else var k
    | Lam t'' -> lam (subst (shift 1 0 s) (j + 1) t'')
    | App (t1, t2) -> app (subst s j t1, subst s j t2))
  

(*Beta reduction*)
let rec reduce t =
  match t with
  | Hc t'->
    (match t' with
    | App (Hc (Lam t1), t2) -> shift (-1) 0 (subst (shift 1 0 t2) 0 t1)
    | App (e1, e2) ->
      let e1' = reduce e1 in
      if e1' <> e1 then app (e1', e2)
      else 
        let e2' = reduce e2 in app (e1, e2')
    | Lam (e) -> lam (reduce e) (* reduce under the lambda (!) *)
    | _ -> Hc t')

let bigstep_reduce_with_count e =
  let rec helper e count =
    let e' = reduce e in
    if e' = e then (e, count)
    else helper e' (count+1)
  in helper e 0

(*Pretty printing*)
let rec print_term t = 
  match t with
  | Hc (t') ->
    match t' with
    | Var k -> print_int k;
    | Lam t' -> print_string "(\\"; print_term t'; print_string ")"
    | App (t1, t2) -> print_string "("; print_term t1; print_string " "; print_term t2; print_string ")"

let num n = 
  let rec helper n =
    if n= 0 then var 0
    else
      app (var 1, helper (n-1))
    in lam (lam (helper n));;

(*Y*)
let y = lam(app(lam(app(var 1, app(var 0, var 0))), lam(app(var 1, app(var 0, var 0)))))

(*id*)
let id = lam(var 0)

(*booleans*)
let t = lam(lam(var 1))
let f = lam(lam(var 0))
let logical_not = lam(app(app(var 0, f), t))
let logical_and = lam(lam(app(app(var 1, var 0), f)))

(*arithmetic*)
let zero = num 0
let succ = lam(lam(lam(app(var 1, app(app(var 2, var 1), var 0)))))
let pred = lam(lam(lam(app(app(app(var 2, lam(lam(app(var 0, app(var 1, var 3))))), lam(var 1)), lam(var 0)))))
let subtract = lam(lam(app(app(var 0, pred), var 1)))

(*predicates*)
let isZero = lam(app(app(var 0, lam(f)), t))
let leq = lam(lam(app(isZero, app(app(subtract, var 1), var 0))))
let gre = lam(lam(app(logical_not, app(app(leq, var 1), var 0))))
let eq = lam(lam(app(app(logical_and, app(app(leq, var 1), var 0)), app(app(leq, var 0), var 1))))


(*Pairs*)
let pair = lam(lam(lam (app(app(var 0, var 2), var 1))))
let first = lam(app(var 0, lam(lam(var 1))))
let second = lam(app(var 0, lam(lam(var 0))))


(*Lists*)
let empty = lam(lam(var 1))
let cons = lam(lam(lam(lam(app(app(var 0, var 3), var 2)))))
let head = lam(app(app(var 0, f), t))
let tail = lam(app(app(var 0, f), f))
let isEmpty = lam(app(app(var 0, t), lam(lam(f))))

let flip = lam(lam(lam(app(app(var 2, var 0), var 1))))

let rec list_builder = function
  | [] -> empty
  | h::t -> app(app(cons, (num h)), (list_builder t))

(*Return the index of the item in the list if it exists else empty list*)
let fFind = lam(lam(lam(lam(app(app(app(isEmpty, var 1), empty), app(app(app(app(eq, var 2), app(head, var 0)), var 0), app(app(app(var 3, var 2), app(tail, var 1)), app(succ, var 0))))))))
let find = lam(lam(app(app(app(app(y, fFind), var 1), var 0), zero)))

(*Get list element at index i*)
let fGet = lam(lam(lam(lam(app(app(app(isEmpty, var 1), empty), app(app(app(app(eq, var 2), var 0), app(head, var 1)), app(app(app(var 3, var 2), app(tail, var 1)), app(succ, var 0))))))))
let get = lam(lam(app(app(app(app(y, fGet), var 1), var 0), zero)))

(*Merge lists x and y*)
let fMerge = lam(lam(lam(app(app(var 1, var 0), lam(lam(app(app(cons, var 1), app(app(var 4, var 0), var 2))))))))
let merge = app(y, fMerge)

(*Reverse list l*)
let fReverse = lam(lam(lam(app(app(app(isEmpty, var 1), var 0), app(app(var 2, app(tail, var 1)), app(app(cons, app(head, var 1)), var 0))))))
let reverse = lam(app(app(app(y, fReverse), var 0), empty))

(*Remove elements of list l that satisfy condition p*)
let fRemove = lam(lam(lam(app(app(var 0, empty), lam(lam(app(app(app(app(var 3, var 1), id), app(cons, var 1)), app(app(var 4, var 3), var 0))))))))
let remove = app(y, fRemove)

(*quick sort a list l of Church numerals in ascending order*)
let fQuickSort = lam(lam(app(app(var 0, empty), lam(lam(app(app(merge, app(var 3, app(app(remove, app(app(flip, gre), var 1)), var 0))), app(app(cons, var 1), app(var 3, app(app(remove, app(app(flip, leq), var 1)), var 0)))))))))
let quickSort = app(y, fQuickSort)


let my_list = match bigstep_reduce_with_count (list_builder [6;5;4;3;2;1]) with | (x, _) -> x
let sort_with_count = match bigstep_reduce_with_count (app(quickSort, my_list)) with | (x, _) -> x
let _ = print_term sort_with_count
let _ = Gc.full_major()
let _ = Gc.print_stat(stdout)