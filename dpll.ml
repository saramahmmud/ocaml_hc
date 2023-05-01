type expr =
    | ATOM of char
    | NOT of hashconsed
    | AND of hashconsed * hashconsed
    | OR of hashconsed * hashconsed
    | IMPLIES of hashconsed * hashconsed
    | BIIMPLIES of hashconsed * hashconsed
    | TRUE
    | FALSE

and hashconsed = Hc of expr [@@hashconsed]

let atom a = Hc (ATOM a)
let not e = Hc (NOT e)
let and_ (e1, e2) = Hc (AND (e1, e2))
let or_ (e1, e2) = Hc (OR (e1, e2))
let implies (e1, e2) = Hc (IMPLIES (e1, e2))
let biimplies (e1, e2) = Hc (BIIMPLIES (e1, e2))
let true_ = Hc TRUE
let false_ = Hc FALSE

let rec impl x = 
match x with Hc x' -> match x' with
    | IMPLIES(e1, e2)      -> or_(not(impl(e1)), impl(e2))
    | BIIMPLIES(e1, e2)    -> and_(impl(implies(e1, e2)), impl(implies(e2, e1)))

    | ATOM(x)              -> atom(x)
    | NOT(e)               -> not(impl(e))
    | AND(e1, e2)          -> and_(impl(e1), impl(e2))
    | OR(e1, e2)           -> or_(impl(e1), impl(e2))
    | TRUE                 -> true_
    | FALSE                -> false_


let rec neg x = 
  match x with Hc x' -> match x' with
    | NOT(Hc AND(e1, e2))     -> or_(neg(not(e1)), neg(not(e2)))
    | NOT(Hc OR(e1, e2))      -> and_(neg(not(e1)), neg(not(e2)))
    | NOT(Hc NOT(e))          -> neg(e)

    | ATOM(x)              -> atom(x)
    | NOT(e)               -> not(neg(e))
    | AND(e1, e2)          -> and_(neg(e1), neg(e2))
    | OR(e1, e2)           -> or_(neg(e1), neg(e2))
    | IMPLIES(e1, e2)      -> implies(neg(e1), neg(e2))   (* Not expected *)
    | BIIMPLIES(e1, e2)    -> biimplies(neg(e1), neg(e2)) (* ^^^^^^^^^^^^ *)
    | TRUE                 -> true_
    | FALSE                -> false_


let rec dis x = 
  match x with Hc x' -> match x' with
    | OR(e1, Hc AND(e2, e3))  -> and_(dis(or_(e1, e2)), dis(or_(e1, e3)))
    | OR(Hc AND(e1, e2), e3)  -> and_(dis(or_(e1, e3)), dis(or_(e2, e3)))
    | OR(e1, e2)           -> (* I feel like this could be cleaner :/ *)
            let e1' = dis(e1) and e2' = dis(e2) in
                if e1 = e1' && e2 = e2' then or_(e1', e2')
                else dis(or_(e1', e2'))

    | ATOM(x)              -> atom(x)
    | NOT(e)               -> not(dis(e))
    | AND(e1, e2)          -> and_(dis(e1), dis(e2))
    | IMPLIES(e1, e2)      -> implies(dis(e1), dis(e2))   (* Not expected *)
    | BIIMPLIES(e1, e2)    -> biimplies(dis(e1), dis(e2)) (* ^^^^^^^^^^^^ *)
    | TRUE                 -> true_
    | FALSE                -> false_


let rec is_in x = function
    | []                   -> false
    | h :: t               -> if h = x then true else is_in x t


let rec list_trim term = function
    | []                       -> []
    | h :: t                   ->
            if h = term then list_trim term t
            else h :: (list_trim term t)


type expr_list =
    | AND_LIST of expr_list list
    | OR_LIST of expr_list list
    | EXPR of hashconsed

exception Exception of string

let listify expr =
    let rec listificate e = function
        | AND_LIST l               -> (
          match e with Hc e' -> match e' with
                | AND(e1, e2)      -> listificate e2 (listificate e1 (AND_LIST l))
                | OR(e1, e2)       -> AND_LIST((listificate e (OR_LIST [])) :: l)
                | _                -> AND_LIST((EXPR e)::l)
          )
        | OR_LIST l                -> (
          match e with Hc e' -> match e' with
                | OR(e1, e2)       -> listificate e2 (listificate e1 (OR_LIST l))
                | AND(e1, e2)      -> OR_LIST((listificate e (AND_LIST [])) :: l)
                | _                -> OR_LIST((EXPR e)::l)
          )
        | _                        -> raise (Exception "Oops")
    in match expr with
    | Hc AND(e1, e2)                  -> listificate expr (AND_LIST [])
    | Hc OR(e1, e2)                   -> listificate expr (OR_LIST [])
    | _                               -> EXPR(expr)


let rec treeify = function
    | AND_LIST [e]                 -> treeify e
    | OR_LIST [e]                  -> treeify e
    | AND_LIST (h :: t)            -> and_ (treeify h, treeify (AND_LIST t))
    | OR_LIST (h :: t)             -> or_ (treeify h, treeify (OR_LIST t))
    | EXPR e                       -> e
    | _                            -> raise (Exception "Oops")


let cnf e = dis(neg(impl(e)))


type clause = CLAUSE of hashconsed list


let clausal e =
    let rec to_exprlist = function
        | []                        -> []
        | (EXPR x) :: t             -> x :: (to_exprlist t)
    in let rec clausify = function
        | AND_LIST []               -> []
        | AND_LIST((EXPR x)::t)     -> 
            let c = clausify (AND_LIST t) in (CLAUSE [x]) :: c
        | AND_LIST((OR_LIST ol)::t) ->
            let c = clausify (AND_LIST t) in (CLAUSE (to_exprlist ol)) :: c
        | e                        -> clausify (AND_LIST [e])
    in clausify (listify (cnf e))


let rec is_taut = function
    | CLAUSE []                   -> false
    | CLAUSE ((Hc(NOT h))::t)         -> if is_in h t then true else is_taut (CLAUSE t)
    | CLAUSE (h::t)               -> if is_in (not h) t then true else is_taut (CLAUSE t)


let rec setify l =
    let rec setificate = function
        | CLAUSE []               -> CLAUSE []
        | CLAUSE (h::t)           ->
                let CLAUSE t' = setificate (CLAUSE t)
                in if is_in h t' then CLAUSE t' else CLAUSE (h::t')
    in match l with
        | []                      -> []
        | h::t                    ->
                let t' = setify t
                in if is_in h t' then t' else h::t'


let rec unit_prop al =
    let rec prop = function
        | (l, [])              -> l
        | (l, ((CLAUSE [x])::t)) ->
            let rec rem_containers = function
                | []           -> []
                | (CLAUSE h)::t         ->
                    if is_in x h then rem_containers t
                    else (CLAUSE h) :: (rem_containers t)
            in let rec trim_neg = function
                | []           -> []
                | h::t         -> (
                    match x with
                        | Hc (NOT x') -> if h = x' then trim_neg t else h :: (trim_neg t)
                        | _      -> if h = not x then trim_neg t else h :: (trim_neg t)
                )
            in let rec trim_neg_all = function
                | []            -> []
                | (CLAUSE h)::t -> (CLAUSE (trim_neg h)) :: (trim_neg_all t)
            in prop (trim_neg_all (rem_containers l), trim_neg_all (rem_containers t))
        | (l, h::t)            -> prop (h::l, t)
    in prop ([], al)


let rec dpll_l al =
    let rec trim_tauts = function
        | []                       -> []
        | h::t                     ->
            if is_taut h then trim_tauts t
            else let t' = trim_tauts t in h :: t'
    in let get_first_atom = function
        | (CLAUSE ((Hc(NOT h))::_))::_ -> h
        | (CLAUSE (h::_))::_       -> h
    in let l = trim_tauts (setify al)
    in match l with
        | []                       -> false
        | _                        -> 
            if is_in (CLAUSE []) l then true
            else dpll_l (unit_prop ((CLAUSE [get_first_atom l])::l))
                && dpll_l (unit_prop ((CLAUSE [not (get_first_atom l)])::l))


let dpll e = dpll_l (clausal (not e))


open Format


let rec pp_expr ppf x = 
  match x with Hc x' -> match x' with
    | ATOM(x)              -> fprintf ppf "%c" x
    | NOT(e)               -> fprintf ppf "¬%a" pp_expr e
    | AND(e1, e2)          -> fprintf ppf "(%a ∧ %a)" pp_expr e1 pp_expr e2
    | OR(e1, e2)           -> fprintf ppf "(%a ∨ %a)" pp_expr e1 pp_expr e2
    | IMPLIES(e1, e2)      -> fprintf ppf "(%a → %a)" pp_expr e1 pp_expr e2
    | BIIMPLIES(e1, e2)    -> fprintf ppf "(%a ↔ %a)" pp_expr e1 pp_expr e2
    | TRUE                 -> fprintf ppf "true"
    | FALSE                -> fprintf ppf "false"


let rec pp_clauseset ppf e =
    let rec pp_clause ppf' l = 
        match l with
            | []               -> fprintf ppf' ""
            | [x]              -> fprintf ppf' "%a" pp_expr x
            | (h::t)           -> fprintf ppf' "%a, %a" pp_expr h pp_clause t
    in match e with
        | []               -> fprintf ppf ""
        | (CLAUSE l)::t    -> fprintf ppf "{ %a } %a" pp_clause l pp_clauseset t


let pp_e e = fprintf std_formatter "%a\n" pp_expr e
let pp_c e = fprintf std_formatter "%a\n" pp_clauseset e 


exception LexingError of int * string


let lexer stream =
    let rec lex pos stream =
        let prefix str =
            let rec prfx i =
                if pos + i < (String.length stream)
                   && i < (String.length str)
                   && stream.[pos + i] = str.[i] then prfx (i + 1)
                else if i >= (String.length str) then true
                else false
            in prfx 0
        in
        if pos >= (String.length stream) then []
        else if prefix "BIIMPLIES" then
            match lex (pos + 9) stream with
                | a :: b :: t   -> biimplies(a, b) :: t
                | _            -> raise (LexingError (pos, "Not enough arguments"))
        else if prefix "IMPLIES" then
            match lex (pos + 7) stream with
                | a :: b :: t   -> implies(a, b) :: t
                | _            -> raise (LexingError (pos, "Not enough arguments"))
        else if prefix "FALSE" then false_ :: (lex (pos + 5) stream)
        else if prefix "TRUE" then true_ :: (lex (pos + 4) stream)
        else if prefix "AND" then
            match lex (pos + 3) stream with
                | a :: b :: t   -> and_(a, b) :: t
                | _            -> raise (LexingError (pos, "Not enough arguments"))
        else if prefix "NOT" then
            match lex (pos + 3) stream with
                | a :: t      -> not(a) :: t
                | _            -> raise (LexingError (pos, "Not enough arguments"))
        else if prefix "OR" then
            match lex (pos + 2) stream with
                | a :: b :: t   -> or_(a, b) :: t
                | _            -> raise (LexingError (pos, "Not enough arguments"))
        else if prefix " " then lex (pos + 1) stream
        else atom(stream.[pos]) :: (lex (pos + 1) stream)
    in match lex 0 stream with
        | [a]              -> a
        | _                -> raise (LexingError (0, "Multiple expressions found"))



let p = atom 'p'
let q = atom 'q'
let r = atom 'r'
let s = atom 's'
let t = atom 't'
let u = atom 'u'
let v = atom 'v'
let w = atom 'w'
let x = atom 'x'
let y = atom 'y'
let z = atom 'z'

let expr =
  and_ (or_ (p, not q),
        and_ (or_ (q, not r),
            and_ (or_ (r, not s),
                  and_ (or_ (s, not t),
                      and_ (or_ (t, not u),
                            and_ (or_ (u, not v),
                                and_ (or_ (v, not w),
                                      and_ (or_ (w, not x),
                                          and_ (or_ (x, not y),
                                                and_ (or_ (y, not z),
                                                    or_ (p, or_ (q, or_ (r, or_ (s, or_ (t, or_ (u, or_ (v, or_ (w, or_ (x, or_ (y, z))))))))))))))))))))
                                        
let _ = Printf.printf "%b\n" (dpll (implies (expr, true_)))

