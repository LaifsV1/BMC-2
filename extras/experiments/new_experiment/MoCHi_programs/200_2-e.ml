let rec copy x = if x=0 then 0 else 1 + copy (x-1)
let m1 n = assert (copy (copy n) = n)

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

let make_array21 n i = assert (0 <= i && i < n); 0
let update21 i a x j :int= if j > i-1 && j <= i then x else a (j)
let rec init i n a =
  if i >= n then a else init (i + 1) n (update21 i a 1)
let m21 k n i =
  if k >= 0 && k <= 0 then
    let x = init k n (make_array21 n) in
      if 0 <= i && i < n then
        assert (x i >= 1)

let rec mc91 x =
  if x > 100 then
		  x - 10
  else
		  mc91 (mc91 (x + 11))
let m22 n = if n <= 102 then assert (mc91 n = 91)

let make_array23 n i = n - i
let rec array_max23 (n:int) i (a:int->int) m =
  if i >= n then
    m
  else
    let x = a i in
    let z = if x>m then x else m in
    array_max23 n (i+1) a z
let m23 n i =
  if n>0 && i>=0 && i<=0 then
    let m = array_max23 n i (make_array23 n) (-1) in
    assert (m >= n)

let make_array24 n i = n - i
let rec array_max24 (n:int) i (a:int->int) m =
  if i >= n then
    m
  else
    let x = a i in
    let z = if x>m then x else m in
    array_max24 n (i+1) a z
let m24 n i =
  if n>0 && i>=0 && i<=0 then
    let m = array_max24 n i (make_array24 n) (-1) in
    assert (not (m = n))

let rec mult25 n m =
  if n <= 0 || m <= 0 then
    0
  else
    n + mult25 n (m-1)
let m25 n m = 
assert (mult25 m m <= mult25 n n)

let rec mult26 n m =
  if n <= 0 || m <= 0 then
    0
  else
    n + mult26 n (m-1)
let m26 n m = 
assert (n*2 <= mult26 n m)

let make_array27 n i = assert (0 <= i && i < n); 0
let update27 i a x j :int= if j > i-1 && j <= i then x else a (j)
let rec init27 i n a =
  if i >= n then a else init27 (i + 1) n (update27 i a 1)
let m27 k n i =
  if k >= 0 && k <= 0 then
    let x = init27 k n (make_array27 n) in
      if 0 <= i && i < n then
        assert (x i = 1)

let rec sum28 n m =
  if n <= 0 then
    m
  else
    1 + sum28 (n-1) m

let rec mult_sum n m =
  if n <= 0 then
    0
  else
    if n == 1 then
      m
    else
      sum28 m (mult_sum (n-1) m)

let m28 n m = assert (mult_sum n m == (n * m))



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
if n = 21 then m21 m m m
else
if n = 22 then m22 m
else
if n = 23 then m23 m m
else
if n = 24 then m24 m m
else
if n = 25 then m25 m m
else
if n = 26 then m26 m m
else
m27 m m m
