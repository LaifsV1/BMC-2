let rec mult n m =
  if n <= 0 || m <= 0 then
    0
  else
    n + mult n (m-1)
let main n m = 
assert (n*2 <= mult n m)
