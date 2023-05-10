
let rec pairwise_compare lst =
  match lst with
  | [] -> []
  | x :: xs ->
    let cmp x y = 
      (assert ((Obj.tag (Obj.repr x)) = 252);
      assert ((Obj.tag (Obj.repr y)) = 252);
      assert((String.compare x y)=0);) 
    in
    let pairs = List.map (fun y -> (x, y)) xs in
    List.iter (fun (a, b) -> cmp a b) pairs;
    pairwise_compare xs
in

let create_string a = "The quick brown fox jumps over the lazy dog" @-@ (if (a > -1) then "!" else "") in
let t  = create_string 0 in
let x = ref [t] in

for i = 0 to 10000 - 2 do
  let y = create_string i in
  x :=  y :: !x;   
done;

let _ = pairwise_compare !x in

Gc.full_major();
Gc.print_stat(stdout)
