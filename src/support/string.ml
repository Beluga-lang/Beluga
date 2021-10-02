include Stdlib.String

let unpack s =
  let n = length s in
  let rec go i = match () with
    | () when i < n -> get s i :: go (i + 1)
    | () -> []
  in
  go 0

let pack cs =
  concat "" (List.map (make 1) cs)

let drop n s = sub s n (length s - n)

let equals s1 s2 = Stdlib.(=) s1 s2
