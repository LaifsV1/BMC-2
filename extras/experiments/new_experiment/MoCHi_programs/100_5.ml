let rec fact n exn =
  if n <= 0 then
    exn 0
  else
    let exn n = if n = 0 then 1 else exn n in
    n * fact (n - 1) exn
let exn n = (assert false:unit); 1
let m2 n = if n > 0 then (let x = fact n exn in ())

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

let rec mc91 x =
  if x > 100 then
		  x - 10
  else
		  mc91 (mc91 (x + 11))
let m133 n = if n <= 102 then assert (mc91 n = 91)

let f18 g x y : int = g (x + 1) (y + 1)
let rec unzip x k =
  if x=0 then
    k 0 0
  else
    unzip (x - 1) (f18 k)
let rec zip x y =
  if x = 0 then
    if y = 0 then
      0
    else
      assert false
  else
    if y = 0 then
      assert false
    else
      1 + zip (x - 1) (y - 1)
let m18 n = unzip n zip

let rec mult n m =
  if n <= 0 || m <= 0 then
    0
  else
    n + mult n (m-1)
let m16 n = assert (n <= mult n n)

let f3 n k = if n >= 0 then () else k 0
let g3 n = assert (n = 0)
let m3 n = f3 n g3


let main n m =
if n = 2 then m2 m
else
if n = 3 then m133 m
else
if n = 5 then let x = m18 m in ()
else
if n = 6 then m6 m
else
if n = 7 then m7 m
else
if n = 9 then m16 m
else
m3 m

