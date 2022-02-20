module Error = OptSpec.Error

type +'a option_specification = 'a OptInfo.Unchecked.t

type 'a option_specification_step = 'a OptInfo.Unchecked.transform

type 'a option_specification_steps = 'a option_specification_step list

let long_name = OptInfo.Unchecked.long_name

let short_name = OptInfo.Unchecked.short_name

let other_names = OptInfo.Unchecked.other_names

let help_message = OptInfo.Unchecked.help_message

let default_argument = OptInfo.Unchecked.default_argument

let meta_variables = OptInfo.Unchecked.meta_variables

let optional = OptInfo.Unchecked.optional

type help_printer = OptSpec.help_printer

type 'a options_specification = 'a OptSpec.t

let opt0 = OptSpec.opt0

let opt1 = OptSpec.opt1

let bool_opt1 = OptSpec.bool_opt1

let int_opt1 = OptSpec.int_opt1

let string_opt1 = OptSpec.string_opt1

let switch_opt = OptSpec.switch_opt

let impure_opt0 = OptSpec.impure_opt0

let help_opt0 = OptSpec.help_opt0

let rest_args = OptSpec.rest_args

let ( <$ ) = OptSpec.( <$ )

let ( <& ) = OptSpec.( <& )

let ( $> ) = OptSpec.( $> )

let ( <! ) = OptSpec.( <! )

let parse = Parser.parse
