open Support
open Beluga_syntax

type error =
  | FixedFixed
    of string (* e.g. "function foo" *)
       * Location.t (* definition location of that item *)
       * Id.cid_prog (* theorem from whose POV the item is out of scope *)
  | FloatingFloating
    of Id.cid_prog
       * Id.cid_prog

exception Error of Location.t * error
let throw loc e = raise (Error (loc, e))

(** Perform late scopechecking for a theorem-theorem interaction.
    thm_thm loc cid mcid
    checks that the theorem identified by `cid` is in scope for the
    theorem specified by `mcid`, if any.
 *)
let thm_thm loc cid1 =
  let get_decl cid = Store.Cid.Comp.( (get cid).Entry.decl ) in
  let name = Store.Cid.Comp.name cid1 in
  let loc' = Name.location name in
  function
  | None -> () (* no cid from whose POV to do the scopechecking *)
  | Some cid2 ->
     match get_decl cid1, get_decl cid2 with
     | Some d1, Some d2 when Bool.not Decl.(d1 < d2) ->
        FixedFixed (Format.asprintf "theorem %a" Name.pp name, loc', cid2)
        |> throw loc
     | None, Some _ ->
        Error.raise_violation
          "[thm_thm] floating-fixed interaction is impossible"
     | None, None ->
        FloatingFloating (cid1, cid2)
        |> throw loc
     | _ ->
        (* catch-all for the 2 allowed cases:
           1. d1 is indeed in scope for d2
           2. a floating theorem can always refer to a fixed theorem
         *)
        ()

(** Performs late scopechecking for a other-theorem interaction.
    other_thm loc name d loc' mcid
    checks that the declaration `d` located at `loc'` is in scope for
    the theorem specified by `mcid`, if any.
 *)
let other_thm loc name d1 loc' = function
  | None -> ()
  | Some cid ->
     match Store.Cid.Comp.( (get cid).Entry.decl ) with
     | None -> ()
     | Some d2 ->
        if Bool.not Decl.(d1 < d2) then
          FixedFixed (name, loc', cid)
          |> throw loc

let () =
  Error.register_exception_printer (function
    | Error (location, FixedFixed (item_name, item_loc, thm_cid)) ->
        let e = Store.Cid.Comp.get thm_cid in
        let thm_name = e.Store.Cid.Comp.Entry.name in
        let thm_loc = Name.location thm_name in
        Error.located_exception_printer
          (Format.dprintf
             "@[<v 0>Ill-scoped reference.@,\
              The %s cannot be referred to from theorem %a.@,\
              - @[<hov>%a@]@]" item_name Name.pp thm_name
             Format.pp_print_text
             "Hint: If you are using Harpoon, you may want to save your \
              work, reorder some definitions, and try again.")
          (List1.from location [ item_loc; thm_loc ])
    | Error (location, FloatingFloating (cid1, cid2)) ->
        let name1 = Store.Cid.Comp.name cid1 in
        let name2 = Store.Cid.Comp.name cid2 in
        Error.located_exception_printer
          (Format.dprintf
             "@[<v>Ill-scoped reference.@,\
              Theorems@,\
             \  @[%a@]@,\
              and@,\
             \  @[%a@]@,\
              cannot refer to each other.@,\
              - @[<hov>%a@]@,\
              - @[<hov>%a@]@,\
              - @[<hov>%a@]@]" Name.pp name1 Name.pp name2
             Format.pp_print_text
             "The theorems have not been materialized in the signature, so \
              their relative scoping cannot be established."
             Format.pp_print_text
             "Hint: If you are using Harpoon, saving your work will \
              materialize the theorems, ordering them. If necessary, use a \
              text editor to adjust the order appropriately."
             Format.pp_print_text
             "Hint: For theorems to be proven mutually, they must be \
              defined together in the same mutual group. In Harpoon, that \
              means configuring both of them within the same interactive \
              prompt. This can be fixed post hoc in a text editor by using \
              `and` between the theorems.")
          (List1.singleton location)
    | exn -> Error.raise_unsupported_exception_printing exn)
