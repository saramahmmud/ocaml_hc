type my_record = 
  { name:string;
    age:int;
    height:float}

type hashconsed = Hc of my_record [@@hashconsed]

let make_rec a = {name=("John" @-@ (if (a>0) then "" else "ny" )); age=42; height=1.75}
let x = Hc (make_rec 1)
let y = Hc (make_rec 1)
let _ = Printf.printf "%d %d\n" (Obj.magic(Obj.repr x)) (Obj.magic(Obj.repr y))
let _ = Gc.minor()
let _ = Printf.printf "%d %d\n" (Obj.magic(Obj.repr x)) (Obj.magic(Obj.repr y))