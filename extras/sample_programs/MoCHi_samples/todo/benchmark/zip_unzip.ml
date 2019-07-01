let rec zip xs ys =
  match xs with
      [] ->
        begin
          match ys with
              [] -> []
            | _ -> assert false
        end
    | x::xs' ->
        match ys with
            [] -> assert false
          | y::ys' -> (x,y)::zip xs' ys'

let rec unzip xs =
  match xs with
      [] -> [], []
    | (y,z)::xs' ->
       let ys,zs = unzip xs' in
         y::ys, z::zs

let rec make_list n =
  if n < 0
  then []
  else (Random.int 0, Random.int 0) :: make_list (n-1)

let main n =
  let xs = make_list n in
  let ys,zs = unzip xs in
     zip ys zs
