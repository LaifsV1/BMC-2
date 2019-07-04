let rec copy x = if x=0 then 0 else 1 + copy (x-1)
let m1 n = assert (copy (copy n) = n)

let rec fact n exn =
  if n <= 0 then
    exn 0
  else
    let exn n = if n = 0 then 1 else exn n in
    n * fact (n - 1) exn
let exn n = (assert false:unit); 1
let m2 n = if n > 0 then (fact n exn; ())

let f3 n k = if n >= 0 then () else k 0
let g3 n = assert (n = 0)
let m3 n = f3 n g3

let c4 (q:int) = ()
let b4 x (q:int) : unit = x 1
let a4 (x:int->unit) (y:int->unit) q = if q=0 then (x 0; y 0) else assert false
let rec f n x q = if n <= 0 then x q else a4 x (f (n-1) (b4 x)) q
let s4 n q = f n c4 q
let m4 n = s4 n 0

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

let max max2 (x:int) (y:int) (z:int) : int = max2 (max2 x y) z
let f9 x y : int = if x >= y then x else y
let m9 (x:int) y z =
  let m = max f9 x y z in
  assert (f9 x m = m)

let rec mc91 x =
  if x > 100 then
    x - 10
  else
    mc91 (mc91 (x + 11))
let m10 n = if n <= 101 then assert (mc91 n = 91)

let main n m =
if n = 1 then m1 m
else
if n = 2 then m2 m
else
if n = 3 then m3 m
else
if n = 4 then m4 m
else
if n = 5 then m5 m
else
if n = 6 then m6 m
else
if n = 7 then m7 m
else
if n = 9 then m9 m m m
else
m10 m
