module LF = struct
  let elaborate_kind kind = Obj.magic ()

  let elaborate_typ typ = Obj.magic ()

  let elaborate_term term = Obj.magic ()
end

module Comp = struct
  let elaborate_kind kind = Error.not_implemented' "[Comp.elaborate_kind]"

  let elaborate_typ typ = Error.not_implemented' "[Comp.elaborate_typ]"

  let elaborate_exp exp = Error.not_implemented' "[Comp.elaborate_exp]"

  let elaborate_pattern pattern =
    Error.not_implemented' "[Comp.elaborate_pattern]"
end

module Harpoon = struct
  let elaborate_repl_command command =
    Error.not_implemented' "[Harpoon.elaborate_command]"
end

module Sgn = struct
  let elaborate_sgn sgn = Error.not_implemented' "[Sgn.elaborate_sgn]"

  let elaborate_numeric_order order =
    Error.not_implemented' "[Sgn.elaborate_numeric_order]"
end

let name_of_identifier identifier =
  Error.not_implemented' "[name_of_identifier]"

let name_of_qualified_identifier qualified_identifier =
  Error.not_implemented' "[name_of_qualified_identifier]"
