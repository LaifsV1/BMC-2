let rec sum n m =
  if n <= 0 then
    m
  else
    1 + sum (n-1) m

let rec mult_sum n m =
  if n <= 0 then
    0
  else
    if n == 1 then
      m
    else
      sum m (mult_sum (n-1) m)

let main n m = assert (mult_sum n m == (n * m))
