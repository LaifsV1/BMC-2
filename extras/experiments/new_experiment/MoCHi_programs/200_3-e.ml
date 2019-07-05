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

let rec f19 g x = if x>=0 then g x else f19 (f19 g) (g x)
let succ x = x+1
let m19 n = assert (f19 succ n >= 0)

let rec ackermann m n =
  if m=0 then
    n+1
  else if n=0 then
    ackermann (m-1) 1
  else
    ackermann (m-1) (ackermann m (n-1))
let m20 m n = if (m>=0 && n>=0) then assert (ackermann m n >= n)

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
if n = 17 then m17 m
else
if n = 18 then m18 m
else
if n = 19 then m19 m
else
if n = 20 then m20 m m
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
if n = 27 then m27 m m m
else
m28 m m; ()
