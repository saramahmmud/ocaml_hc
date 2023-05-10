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

type s =
| Foo of bool
| Baz of int
| Bar of string

type t =
CoolConstructor of s * s [@@hashconsed]

let createT a = CoolConstructor ((Foo (a mod 2 == 0)), (Baz (a mod 3)))
let createString a = string_of_int a

let _ =
  let a = createT 2 in 
  let b = createT 2 in
  let c = Bar (createString 4) in
  Printf.printf "Result of comparison (variants) before is %b\n" (a == b);
  Printf.printf "The pointer value of a is %d\n" (Obj.magic a);
  Printf.printf "The pointer value of b is %d\n" (Obj.magic b);
  Gc.minor();
  Printf.printf "Result of comparison (variants) after is %b\n" (a == b);
  Printf.printf "The pointer value of a is %d\n" (Obj.magic a);
  Printf.printf "The pointer value of b is %d\n" (Obj.magic b);
  (match a with
  | CoolConstructor (Foo (x), Baz (y)) -> Printf.printf "The value of x is %b and the value of y is %d\n" x y
  | _ -> Printf.printf "Something went wrong\n");
  (match c with
  | Foo (x) -> Printf.printf "The value of x is %b\n" x
  | Baz (y) -> Printf.printf "The value of y is %d\n" y
  | Bar (z) -> Printf.printf "The value of z is %s\n" z)

let _ = 
  let c = createString 2 in
  let d = createString 2 in
  Printf.printf "Result of comparison (string) before is %b\n" (c == d);
  Gc.minor();
  Printf.printf "Result of comparison (string) after is %b\n" (c == d)
