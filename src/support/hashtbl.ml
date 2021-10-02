include Stdlib.Hashtbl

let map f h =
  to_seq h
  |> Seq.map (fun (k, x) -> (k, f x))
  |> of_seq

let group_by p l =
  let h = create 32 in
  let () =
    let insert k x =
      let d =
        match find_opt h k with
        | None -> DynArray.make 32
        | Some d -> d
      in
      DynArray.add d x;
      replace h k d
    in
    List.iter (fun x -> insert (p x) x) l
  in
  map DynArray.to_list h
