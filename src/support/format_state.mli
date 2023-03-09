include module type of Format

module type S = sig
  include State.STATE

  val pp_flush : Unit.t t

  val pp_newline : Unit.t t

  val pp_nop : Unit.t t

  val pp_cut : Unit.t t

  val pp_space : Unit.t t

  val pp_non_breaking_space : Unit.t t

  val pp_break : Int.t -> Int.t -> Unit.t t

  val pp_as : Int.t -> String.t -> Unit.t t

  val append : Unit.t t -> Unit.t t -> Unit.t t

  val ( ++ ) : Unit.t t -> Unit.t t -> Unit.t t

  val pp_box : ?indent:Int.t -> Unit.t t -> Unit.t t

  val pp_hbox : Unit.t t -> Unit.t t

  val pp_vbox : ?indent:Int.t -> Unit.t t -> Unit.t t

  val pp_hvbox : ?indent:Int.t -> Unit.t t -> Unit.t t

  val pp_hovbox : ?indent:Int.t -> Unit.t t -> Unit.t t

  val pp_bool : Bool.t -> Unit.t t

  val pp_int : Int.t -> Unit.t t

  val pp_float : Float.t -> Unit.t t

  val pp_char : Char.t -> Unit.t t

  val pp_string : String.t -> Unit.t t

  val pp_option :
    ?none:Unit.t t -> ('a -> Unit.t t) -> 'a Option.t -> Unit.t t

  val pp_list : ?sep:Unit.t t -> ('a -> Unit.t t) -> 'a List.t -> Unit.t t

  val pp_list1 : ?sep:Unit.t t -> ('a -> Unit.t t) -> 'a List1.t -> Unit.t t

  val pp_list2 : ?sep:Unit.t t -> ('a -> Unit.t t) -> 'a List2.t -> Unit.t t

  val pp_text : String.t -> Unit.t t

  val pp_utf_8 : String.t -> Unit.t t

  val pp_utf_8_text : String.t -> Unit.t t
end

module Make (S : sig
  include State.STATE

  val with_formatter : (formatter -> 'a t) -> 'a t
end) : S with type state = S.state
