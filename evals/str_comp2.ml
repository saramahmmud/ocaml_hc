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

let physically_equal = ref 0 in

let rec pairwise_compare lst =
  match lst with
  | [] -> []
  | x :: xs ->
    let cmp x y = 
      (assert ((Obj.tag (Obj.repr x)) = 252);
      (if (x == y) then physically_equal := !physically_equal + 1); 
      assert((String.compare x y)=0);) 
    in
    let pairs = List.map (fun y -> (x, y)) xs in
    List.iter (fun (a, b) -> cmp a b) pairs;
    pairwise_compare xs
in

let t  = String.make 200 'a' in
let x = ref [t] in

for i = 0 to 10000 - 2 do
  let y = String.make 200 'a' in
  x :=  y :: !x;   
done;

Gc.minor();
let _ = pairwise_compare !x in
let _ = Printf.printf "physical: %i\n" (!physically_equal) in

Gc.full_major();
Gc.print_stat(stdout)