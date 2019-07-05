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


let main n m =
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
if n = 19 then m19 m
else
if n = 20 then m20 m m
else
m21 m m m
