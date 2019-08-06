(** Gets the version of Beluga from the dune-build.info library. *)
let get () =
  match Build_info.V1.version () with
  | None -> "n/a"
  | Some v -> Build_info.V1.Version.to_string v
