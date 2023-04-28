(** Format combinators using the {!module:Format} module, but using a state
    having a {!type:Format.formatter} state.

    This is used to faciliate pretty-printing using a custom definition of
    state. In particular, pretty-printing of the external syntax requires
    keeping track of constant declarations and notation pragmas while a
    Beluga signature is being pretty-printed. *)

open Format

(** Abstract definition of a formatter. *)
module type S = sig
  (** @closed *)
  include Imperative_state.IMPERATIVE_STATE

  (** [pp_flush state] is analogous to {!val:Format.pp_print_flush}. *)
  val pp_flush : state -> Unit.t

  (** [pp_newline state] is analogous to {!val:Format.pp_print_newline}. *)
  val pp_newline : state -> Unit.t

  (** [pp_nop state] is [()]. This is useful to signal that nothing should be
      printed for some execution branch. *)
  val pp_nop : state -> Unit.t

  (** [pp_cut state] is analogous to {!val:Format.pp_print_cut}. *)
  val pp_cut : state -> Unit.t

  (** [pp_space state] is analogous to {!val:Format.pp_print_space}. Note
      that this is a possibly breaking space, meaning that a newline may be
      printed at this point. *)
  val pp_space : state -> Unit.t

  (** [pp_non_breaking_space state] pretty-prints a non-breaking space,
      meaning that the printer does not insert break directives to that
      space. *)
  val pp_non_breaking_space : state -> Unit.t

  (** [pp_break state width offset] is analogous to
      {!val:Format.pp_print_break}. *)
  val pp_break : state -> Int.t -> Int.t -> Unit.t

  (** [pp_as state size] is analogous to {!val:Format.pp_print_as} to
      pretty-print a string as if it were of length [size]. This is useful to
      pretty-print UTF-8 encoded strings of known codepoint count, or to
      print a string as if it isn't there, like for HTML tags or ASCII escape
      sequences. *)
  val pp_as : state -> Int.t -> String.t -> Unit.t

  (** [pp_box state ?(indent = 0) f] evaluates [f state] in a compacting
      pretty-printing box wth offset [indent] in the formatter (see
      {!val:Format.pp_open_box}). The box is opened before [f state], and
      closed afterwards. *)
  val pp_box : state -> ?indent:Int.t -> (state -> Unit.t) -> Unit.t

  (** [pp_hbox state f] evaluates [f state] in a horizontal pretty-printing
      box (see {!val:Format.pp_open_hbox}). The box is opened before
      [f state], and closed afterwards. *)
  val pp_hbox : state -> (state -> Unit.t) -> Unit.t

  (** [pp_vbox state ?(indent = 0) f] evaluates [f state] in a vertical
      pretty-printing box with offset [indent] (see
      {!val:Format.pp_open_vbox}). The box is opened before [f state], and
      closed afterwards. *)
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
end

(** Functor constructing a concrete instance of a formatter. *)
module Make (State : sig
  type state

  val get_formatter : state -> formatter
end) : S with type state = State.state
