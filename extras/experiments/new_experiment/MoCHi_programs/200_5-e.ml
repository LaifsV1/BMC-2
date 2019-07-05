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

let succ x = x + 1
let rec repeat (f:int->int) n s : int =
  if n = 0 then
    s
  else
    f (repeat f (n-1) s)
let m16 n = assert (repeat succ n 0 > n)

let lock st = assert (st=0); 1
let unlock st = assert (st=1); 0
let f17 n st : int= if n > 0 then lock (st) else st
let g17 n st : int = if n >= 0 then unlock (st) else st
let m17 n = assert ((g17 n (f17 n 0)) = 0)

let rec sum n =
  if n <= 0 then
    0
  else
    n + sum (n-1)
let m18 n = assert (n+1 <= sum n)

let make_array21 n i = assert (0 <= i && i < n); 0
let update21 i a x j :int= if j > i-1 && j <= i then x else a (j)
let rec init i n a =
  if i >= n then a else init (i + 1) n (update21 i a 1)
let m21 k n i =
  if k >= 0 && k <= 0 then
    let x = init k n (make_array21 n) in
      if 0 <= i && i < n then
        assert (x i >= 1)

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

let main n m =
if n = 7 then m7 m
else
if n = 9 then m9 m m m
else
if n = 11 then m11 m
else
if n = 12 then m12 m
else
if n = 13 then m13 m
else
if n = 14 then m14 m
else
if n = 15 then m15 m
else
if n = 16 then m16 m
else
if n = 17 then m17 m
else
if n = 18 then m18 m
else
if n = 21 then m21 m m m
else
m23 m m

