type state

val fprintf : state -> ('a, Format.formatter, Unit.t) format -> 'a

val create_initial_state : Unit.t -> state

val print_usage : state -> Unit.t

val interpret_command : state -> input:String.t -> Unit.t

val load : state -> filename:String.t -> Synint.Sgn.sgn
