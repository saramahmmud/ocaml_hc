let x = "hello" in
let y = String.sub x 1 3 in
Printf.printf "%d\n" (Obj.tag(Obj.repr y))