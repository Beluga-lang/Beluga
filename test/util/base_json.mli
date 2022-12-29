open Support

(** {1 Transforms} *)

(** [without_field field_to_remove json] is [json] without record fields
    named [field_to_remove]. *)
val without_field : String.t -> Yojson.Safe.t -> Yojson.Safe.t

(** [without_locations json] is [json] without record fields named
    ["location"]. *)
val without_locations : Yojson.Safe.t -> Yojson.Safe.t

(** [without_operators json] is [json] without record fields named
    ["operator"]. *)
val without_operators : Yojson.Safe.t -> Yojson.Safe.t

(** {1 Support} *)

val json_of_association : (String.t * Yojson.Safe.t) List.t -> Yojson.Safe.t

val json_of_int : Int.t -> Yojson.Safe.t

val json_of_bool : Bool.t -> Yojson.Safe.t

val json_of_string : String.t -> Yojson.Safe.t

val json_of_list : ('a -> Yojson.Safe.t) -> 'a List.t -> Yojson.Safe.t

val json_of_list1 : ('a -> Yojson.Safe.t) -> 'a List1.t -> Yojson.Safe.t

val json_of_list2 : ('a -> Yojson.Safe.t) -> 'a List2.t -> Yojson.Safe.t

val json_of_variant :
  name:String.t -> data:(String.t * Yojson.Safe.t) List.t -> Yojson.Safe.t

val json_of_option : ('a -> Yojson.Safe.t) -> 'a Option.t -> Yojson.Safe.t
