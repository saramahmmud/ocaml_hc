type s =
| Foo of bool
| Baz of int
| Bar of string
type t =
CoolConstructor of s * s [@@hashconsed]

let test a = 
  let x = CoolConstructor ((Foo (a mod 2 == 0)) , (Baz (a*a))) in
  Gc.minor();
  Printf.printf "Tag is %d \n" (Obj.tag (Obj.repr x))

let test2 n =
  for i = 0 to n do 
    test i 
  done

let createT a = CoolConstructor ((Foo (a mod 2 == 0)), (Baz (a mod 3)))
let createString a = string_of_int a

let _ =
  let a = createT 2 in 
  let b = createT 2 in
  Printf.printf "Result of comparison (variants) before is %b\n" (a == b);
  Printf.printf "The pointer value of a is %d\n" (Obj.magic a);
  Printf.printf "The pointer value of b is %d\n" (Obj.magic b);
  Gc.minor();
  Printf.printf "Result of comparison (variants) after is %b\n" (a == b);
  Printf.printf "The pointer value of a is %d\n" (Obj.magic a);
  Printf.printf "The pointer value of b is %d\n" (Obj.magic b)

let _ = 
  let c = createString 2 in
  let d = createString 2 in
  Printf.printf "Result of comparison (string) before is %b\n" (c == d);
  Gc.minor();
  Printf.printf "Result of comparison (string) after is %b\n" (c == d)