open Format

module type S = sig
  include Imperative_state.IMPERATIVE_STATE

  val pp_flush : state -> Unit.t

  val pp_newline : state -> Unit.t

  val pp_nop : state -> Unit.t

  val pp_cut : state -> Unit.t

  val pp_space : state -> Unit.t

  val pp_non_breaking_space : state -> Unit.t

  val pp_break : state -> Int.t -> Int.t -> Unit.t

  val pp_as : state -> Int.t -> String.t -> Unit.t

  val pp_box : state -> ?indent:Int.t -> (state -> Unit.t) -> Unit.t

  val pp_hbox : state -> (state -> Unit.t) -> Unit.t

  val pp_vbox : state -> ?indent:Int.t -> (state -> Unit.t) -> Unit.t

  val pp_hvbox : state -> ?indent:Int.t -> (state -> Unit.t) -> Unit.t

  val pp_hovbox : state -> ?indent:Int.t -> (state -> Unit.t) -> Unit.t

  val pp_bool : state -> Bool.t -> Unit.t

  val pp_int : state -> Int.t -> Unit.t

  val pp_float : state -> Float.t -> Unit.t

  val pp_char : state -> Char.t -> Unit.t

  val pp_string : state -> String.t -> Unit.t

  val pp_option :
       state
    -> ?none:(state -> Unit.t)
    -> (state -> 'a -> Unit.t)
    -> 'a Option.t
    -> Unit.t

  val pp_list :
       state
    -> ?sep:(state -> Unit.t)
    -> (state -> 'a -> Unit.t)
    -> 'a List.t
    -> Unit.t

  val pp_list1 :
       state
    -> ?sep:(state -> Unit.t)
    -> (state -> 'a -> Unit.t)
    -> 'a List1.t
    -> Unit.t

  val pp_list2 :
       state
    -> ?sep:(state -> Unit.t)
    -> (state -> 'a -> Unit.t)
    -> 'a List2.t
    -> Unit.t

  val pp_text : state -> String.t -> Unit.t

  val pp_utf_8 : state -> String.t -> Unit.t

  val pp_utf_8_text : state -> String.t -> Unit.t

  val traverse_option :
    state -> (state -> 'a -> 'b) -> 'a Option.t -> 'b Option.t

  val traverse_list : state -> (state -> 'a -> 'b) -> 'a List.t -> 'b List.t

  val traverse_list_void :
    state -> (state -> 'a -> Unit.t) -> 'a List.t -> Unit.t

  val traverse_list1 :
    state -> (state -> 'a -> 'b) -> 'a List1.t -> 'b List1.t

  val traverse_list2 :
    state -> (state -> 'a -> 'b) -> 'a List2.t -> 'b List2.t
end

module Make (State : sig
  type state

  val get_formatter : state -> formatter
end) : S with type state = State.state
