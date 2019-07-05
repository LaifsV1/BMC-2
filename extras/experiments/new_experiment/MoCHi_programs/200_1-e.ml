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

let f8 g x y : int = g (x + 1) (y + 1)
let rec unzip8 x k =
  if x=0 then
    k 0 0
  else
    unzip8 (x - 1) (f8 k)
let rec zip8 x y =
  if x = 0 then
    if y = 0 then
      0
    else
      assert false
  else
    if y = 0 then
      assert false
    else
      1 + zip8 (x - 1) (y - 1)
let m8 n = unzip8 n zip8

let rec mult n m =
  if n <= 0 || m <= 0 then
    0
  else
    n + mult n (m-1)
let m11 n = assert (n <= mult n n)

let make_array n i = assert (0 <= i && i < n); 0
let update (i:int) (n:int) des x : int -> int =
  des i;
  let a j = if i=j then x else des i in a
let print_int (n:int) = ()
let f20 (m:int) src des =
  let rec bcopy (m:int) src des i =
    if i >= m then
      des
    else
      let des = update i m des (src i) in
      bcopy m src des (i+1)
  in
  let rec print_array m (array:int->int) i =
    if i >= m then
      ()
    else
      (print_int (des i);
       print_array m array (i + 1))
  in
  let array : int -> int = bcopy m src des 0 in
    print_array m array 0
let m12 n =
  let array1 = make_array n in
  let array2 = make_array n in
    if n > 0 then f20 n array1 array2

let lock st = assert (st=0); 1
let unlock st = assert (st=1); 0
let f13 n st : int= if n > 0 then lock (st) else st
let g13 n st : int = if n > 0 then unlock (st) else st
let m13 n = assert ((g13 n (f13 n 0)) = 0)

let rec sum n =
  if n <= 0 then
    0
  else
    n + sum (n-1)
let m14 n = assert (n <= sum n)

let rec mult n m =
  if n <= 0 || m <= 0 then
    0
  else
    n + mult n (m-1)
let m15 n = assert (n+1 <= mult n n)



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
if n = 10 then m10 m
else
if n = 11 then m11 m
else
if n = 12 then m12 m
else
if n = 13 then m13 m
else
if n = 14 then m14 m
else
m15 m
