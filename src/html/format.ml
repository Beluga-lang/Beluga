open Support
include Format

module type FORMAT_STATE = sig
  include State.STATE

  val pp_flush : Unit.t t

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
end) : FORMAT_STATE with type state = S.state = struct
  include S

  let nop = return ()

  let pp_nop = nop

  let pp_flush =
    with_formatter (fun ppf ->
        pp_print_flush ppf ();
        nop)

  let pp_cut =
    with_formatter (fun ppf ->
        pp_print_cut ppf ();
        nop)

  let pp_space =
    with_formatter (fun ppf ->
        pp_print_space ppf ();
        nop)

  let pp_non_breaking_space =
    with_formatter (fun ppf ->
        pp_print_char ppf ' ';
        nop)

  let pp_break width offset =
    with_formatter (fun ppf ->
        pp_print_break ppf width offset;
        nop)

  let pp_as width s =
    with_formatter (fun ppf ->
        pp_print_as ppf width s;
        nop)

  let append p1 p2 =
    let* () = p1 in
    p2

  let ( ++ ) = append

  let pp_box ?(indent = 0) p =
    with_formatter (fun ppf ->
        pp_open_box ppf indent;
        let* () = p in
        pp_close_box ppf ();
        nop)

  let pp_hbox p =
    with_formatter (fun ppf ->
        pp_open_hbox ppf ();
        let* () = p in
        pp_close_box ppf ();
        nop)

  let pp_vbox ?(indent = 0) p =
    with_formatter (fun ppf ->
        pp_open_vbox ppf indent;
        let* () = p in
        pp_close_box ppf ();
        nop)

  let pp_hvbox ?(indent = 0) p =
    with_formatter (fun ppf ->
        pp_open_hvbox ppf indent;
        let* () = p in
        pp_close_box ppf ();
        nop)

  let pp_hovbox ?(indent = 0) p =
    with_formatter (fun ppf ->
        pp_open_hovbox ppf indent;
        let* () = p in
        pp_close_box ppf ();
        nop)

  let pp_bool b =
    with_formatter (fun ppf ->
        pp_print_bool ppf b;
        nop)

  let pp_int i =
    with_formatter (fun ppf ->
        pp_print_int ppf i;
        nop)

  let pp_float f =
    with_formatter (fun ppf ->
        pp_print_float ppf f;
        nop)

  let pp_char c =
    with_formatter (fun ppf ->
        pp_print_char ppf c;
        nop)

  let pp_string s =
    with_formatter (fun ppf ->
        pp_print_string ppf s;
        nop)

  let pp_option ?(none = nop) ppv o =
    match o with
    | Option.None -> none
    | Option.Some x -> ppv x

  let rec pp_list ?(sep = nop) ppv l =
    match l with
    | [] -> nop
    | [ x ] -> ppv x
    | x :: xs ->
        let* () = ppv x in
        let* () = sep in
        pp_list ~sep ppv xs

  let pp_list1 ?(sep = nop) ppv l =
    let (List1.T (x, xs)) = l in
    let* () = ppv x in
    let* () = sep in
    pp_list ~sep ppv xs

  let pp_list2 ?(sep = nop) ppv l =
    let (List2.T (x1, x2, xs)) = l in
    let* () = ppv x1 in
    let* () = sep in
    let* () = ppv x2 in
    let* () = sep in
    pp_list ~sep ppv xs

  let pp_text t =
    with_formatter (fun ppf ->
        pp_print_text ppf t;
        nop)

  let pp_utf_8 t =
    with_formatter (fun ppf ->
        pp_utf_8 ppf t;
        nop)

  let pp_utf_8_text t =
    with_formatter (fun ppf ->
        pp_utf_8_text ppf t;
        nop)
end
