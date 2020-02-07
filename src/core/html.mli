type css_file = Options.HTML.css_file

val generate : bool ref
val css : css_file ref
val filename : string option ref
val printing : bool ref
val generatePage : string -> unit

val append : string -> unit
val appendAsComment : string -> unit
val addId : string -> unit
val idExists : string -> bool
