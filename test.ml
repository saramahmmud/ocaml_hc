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

let _ =
  let a = createT 2 in 
  let b = createT 2 in
  Printf.printf "Result of comparison before is %b\n" (a == b);
  Gc.minor();
  Printf.printf "Result of comparison after is %b\n" (a == b)