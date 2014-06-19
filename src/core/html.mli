val genHtml : bool ref
val genCSS : bool ref
val printingHtml : bool ref

val generatePage : string -> unit

val append : string -> unit
val appendAsComment : string -> unit
val addId : string -> unit
val idExists : string -> bool
