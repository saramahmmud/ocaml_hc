type s =
| Foo of bool
| Baz of int
| Bar of string
type t =
CoolConstructor of s [@@hashconsed]

let test a = 
  let _ = CoolConstructor (Foo (a mod 2 == 0)) in
  let _ = CoolConstructor (Baz a) in
  Gc.minor()

let _ =
  for i = 0 to 10 do 
    test i 
  done;