type htmlClass = Kind | Const | None | Fun


val genHtml : bool ref
val ids : string list ref

val generatePage : string -> unit

val appendAsAnchor : string -> string -> htmlClass -> unit
val append : string -> unit
val appendAsComment : string -> unit
