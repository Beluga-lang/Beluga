type htmlClass = Kind | Const | None | Fun


val genHtml : bool ref

val printingHtml : bool ref

val generatePage : string -> unit

val append : string -> unit
val appendAsComment : string -> unit
