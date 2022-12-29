(** [assert_exn f] asserts that [f ()] raises any exception. *)
val assert_exn : (unit -> 'a) -> unit

(** [assert_json_equal ~expected ~actual] asserts that [expected = actual]. *)
val assert_json_equal :
  expected:Yojson.Safe.t -> actual:Yojson.Safe.t -> Unit.t

(** [assert_equal_as_json to_json ~expected ~actual] asserts that
    [to_json expected = to_json actual]. *)
val assert_equal_as_json :
  ('a -> Yojson.Safe.t) -> expected:'a -> actual:'a -> Unit.t
