(** Totally miscellaneous functions. *)

include Equality

(** Runs a function ignoring all exceptions. In general this is a terrible
    idea, but it is sometimes necessary when performing cleanup that may fail
    while in an exception handler. *)
let noexcept f =
  try f () with
  | _ -> ()

(** An exception to be raised in unimplemented features. * Code that raises
    this exception should never be committed. *)
exception NotImplemented of string

let not_implemented (msg : string) : 'a = raise (NotImplemented msg)

(** Forms the tuple of its two inputs. *)
let tuple (x : 'a) (y : 'b) : 'a * 'b = (x, y)

(** Creates a constant function that raises the given exception. Useful when
    eliminating option-types. *)
let throw (e : exn) : 'b -> 'a = fun _ -> raise e
