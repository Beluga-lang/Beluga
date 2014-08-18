type css = Normal | NoCSS | File of string

val genHtml : bool ref
val css : css ref
val filename : string ref
val printingHtml : bool ref
val generatePage : unit -> unit

val append : string -> unit
val appendAsComment : string -> unit
val addId : string -> unit
val idExists : string -> bool
