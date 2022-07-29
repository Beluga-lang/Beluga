module LF = struct
  let elaborate_kind kind = Error.not_implemented' "[LF.elaborate_kind]"

  let elaborate_typ typ = Error.not_implemented' "[LF.elaborate_typ]"

  let elaborate_term term = Error.not_implemented' "[LF.elaborate_term]"
end

module Comp = struct
  let elaborate_kind kind = Error.not_implemented' "[Comp.elaborate_kind]"

  let elaborate_typ typ = Error.not_implemented' "[Comp.elaborate_typ]"

  let elaborate_exp exp = Error.not_implemented' "[Comp.elaborate_exp]"

  let elaborate_pattern pattern =
    Error.not_implemented' "[Comp.elaborate_pattern]"
end

module Harpoon = struct
  let elaborate_command command =
    Error.not_implemented' "[Harpoon.elaborate_command]"
end

module Sgn = struct
  let elaborate_sgn sgn = Error.not_implemented' "[Sgn.elaborate_sgn]"
end
