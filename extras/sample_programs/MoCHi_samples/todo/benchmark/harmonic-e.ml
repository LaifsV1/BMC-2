let rec div x y =
  assert (y <> 0);
  if x < y
  then 0
  else 1 + div (x-y) y

let rec fold_left f acc xs =
  match xs with
      [] -> acc
    | x::xs' -> fold_left f (f acc x) xs'

let rec range i j =
  if i > j then
    []
  else
    let is = range (i+1) j in
      i::is

let harmonic n =
  let ds = range 0 n in
    fold_left (fun s k -> s + div 10000 k) 0 ds
