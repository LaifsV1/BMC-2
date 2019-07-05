let lock12 st = assert (st=0); 1
let unlock12 st = assert (st=1); 0
let f12 n st : int= if n > 0 then lock12 (st) else st
let g12 n st : int = if n > 0 then unlock12 (st) else st
let m12 n = assert ((g12 n (f12 n 0)) = 0)

let rec fact n exn =
  if n <= 0 then
    exn 0
  else
    let exn n = if n = 0 then 1 else exn n in
    n * fact (n - 1) exn
let exn n = (assert false:unit); 1
let m2 n = if n > 0 then (let x = fact n exn in ())

let f3 n k = if n >= 0 then () else k 0
let g3 n = assert (n = 0)
let m3 n = f3 n g3

let f5 x g : unit = g(x+1)
let h5 y = assert (y>0)
let m5 n = if n>0 then f5 n h5

let f6 x g :unit= g(x+1)
let h6 z y = assert (y>z)
let m6 n = if n>=0 then f6 n (h6 n)

let rec zip x y =
  if x = 0 then
    if y = 0 then
      x
    else
      assert false
  else
    if y = 0 then
      assert false
    else
      1 + zip (x - 1) (y - 1)
let rec map x =
  if x = 0 then x else 1 + map (x - 1)
let m7 n =
  assert (map (zip n n) = n)

let rec mult n m =
  if n <= 0 || m <= 0 then
    0
  else
    n + mult n (m-1)
let m16 n = assert (n <= mult n n)

let succ x = x + 1
let rec repeat (f:int->int) n s : int =
  if n = 0 then
    s
  else
    f (repeat f (n-1) s)
let m17 n = assert (repeat succ n 0 > n)


let main n m =
if n = 12 then m12 m
else
if n = 2 then m2 m
else
if n = 3 then m3 m
else
if n = 5 then m5 m
else
if n = 6 then m6 m
else
if n = 7 then m7 m
else
if n = 9 then m16 m
else
m17 m
