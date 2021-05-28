open Support
open Syntax
open Store.Cid

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
  let get_decl cid = Comp.( (get cid).Entry.decl ) in
  let name = Comp.name cid1 in
  let loc' = Id.loc_of_name name in
  let name = Id.render_name name in
  function
  | None -> () (* no cid from whose POV to do the scopechecking *)
  | Some cid2 ->
     match get_decl cid1, get_decl cid2 with
     | Some d1, Some d2 when not Decl.(d1 < d2) ->
        FixedFixed ( "theorem " ^ name, loc', cid2 )
        |> throw loc
     | None, Some _ ->
        Error.violation
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
     match Comp.( (get cid).Entry.decl ) with
     | None -> ()
     | Some d2 ->
        if not Decl.(d1 < d2) then
          FixedFixed (name, loc', cid)
          |> throw loc


let format_error ppf =
  let open Format in
  function
  | FixedFixed (item_name, item_loc, thm_cid) ->
     let e = Comp.get thm_cid in
     let thm_name = e.Comp.Entry.name in
     let thm_loc = Id.loc_of_name thm_name in
     fprintf ppf
       "@[<v>Ill-scoped reference.\
        @,The %s defined at\
        @,@[%a@]\
        @,cannot be referred to from theorem\
        @,  @[%a@]\
        @,defined at\
        @,@[%a@]\
        @,- @[<hov>%a@]@]"
       item_name
       Location.print item_loc
       Id.print thm_name
       Location.print thm_loc
       pp_print_text
       "Hint: If you are using Harpoon, you may want to save your \
        work, reorder some definitions, and try again."

  | FloatingFloating (cid1, cid2) ->
     let (name1, name2) = Pair.both Comp.name (cid1, cid2) in
     fprintf ppf
       "@[<v>Ill-scoped reference.\
        @,Theorems\
        @,  @[%a@]\
        @,and\
        @,  @[%a@]\
        @,cannot refer to each other.\
        @,- @[<hov>%a@]\
        @,- @[<hov>%a@]\
        @,- @[<hov>%a@]@]"
       Id.print name1
       Id.print name2
       pp_print_text
       "The theorems have not been materialized in the signature, so \
        their relative scoping cannot be established."
       pp_print_text
       "Hint: If you are using Harpoon, saving your work will \
        materialize the theorems, ordering them. If necessary, use a \
        text editor to adjust the order appropriately."
       pp_print_text
       "Hint: For theorems to be proven mutually, they must be \
        defined together in the same mutual group. In Harpoon, that \
        means configuring both of them within the same interactive \
        prompt. This can be fixed post hoc in a text editor by using \
        `and` between the theorems."

let _ =
  Error.register_printer
    begin fun (Error (loc, err)) ->
    Error.print_with_location loc
      (fun ppf -> format_error ppf err)
    end
