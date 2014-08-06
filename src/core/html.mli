val genHtml : bool ref
val genCSS : bool ref
val filename : string ref
val printingHtml : bool ref

val generatePage : unit -> unit

val append : string -> unit
val appendAsComment : string -> unit
val addId : string -> unit
val idExists : string -> bool
