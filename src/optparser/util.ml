let id a = a

module List = struct
  include Stdlib.List

  let filter_map f l =
    let rec loop = function
      | [] -> []
      | h :: t ->
        match f h with
        | None -> loop t
        | Some x -> x :: loop t
    in
    loop l
end

module Option = struct
  let some a = Some a

  let fold ~none ~some =
    function
    | None -> none
    | Some a -> some a

  let map f = fold ~none:None ~some:(fun a -> Some (f a))

  let to_list (opt : 'a option) : 'a list =
    fold ~none:[] ~some:(fun a -> [a]) opt
  let to_seq (opt : 'a option) : 'a Seq.t =
    fold ~none:Seq.empty ~some:Seq.return opt
end

module Result = struct
  let ok a = Ok a
  let error e = Error e

  let fold ~error ~ok =
    function
    | Error e -> error e
    | Ok a -> ok a

  let map f = fold ~error ~ok:(fun a -> Ok (f a))
end
