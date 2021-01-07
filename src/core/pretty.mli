(** Pretty printing for external and internal syntax.

    @see http://caml.inria.fr/resources/doc/guides/format.html
*)

(* To add new pretty-printing functions:
   - add declarations in printer.ml
   - add new implementations in prettyint.ml or prettyext.ml
 *)

module Common : Printer.Common.T

module Int : sig
  module Make : functor (_ : Store.Cid.RENDERER) -> Printer.Int.T
  module DefaultPrinter : Printer.Int.T
end

module Ext : sig
  module Make : functor (_ : Store.Cid.RENDERER) -> Printer.Ext.T
  module DefaultPrinter : Printer.Ext.T
end
