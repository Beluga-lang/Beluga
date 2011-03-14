signature TOP =
sig
    (* interactive loop *)
    val loop_print   : unit -> unit
    val loop_type    : unit -> unit
    val loop_eval    : unit -> unit

    val loop         : unit -> unit   (* typechecks, and if typing was successful, evaluates *)

    (* read a MinML source file *)
    val file_print : string -> unit
    val file_type  : string -> unit
    val file_eval  : string -> unit

    val file       : string -> unit  (* typechecks, and if typing was successful, evaluates *)
end

structure Top :> TOP =
struct

    fun loop_type () = 
        (Loop.loop (Loop.check Loop.show))
        handle Parse.Error s => print ("Parse error: " ^ s ^ "\n");

    fun loop_eval () = 
        (Loop.loop (Loop.eval Loop.show))
        handle Parse.Error s => print ("Parse error: " ^ s ^ "\n");
    
    fun loop_print () =
        (Loop.loop Loop.show)
        handle Parse.Error s => print ("Parse error: " ^ s ^ "\n");

    fun loop () =
        (Loop.loop (Loop.usual Loop.show))
        handle Parse.Error s => print ("Parse error: " ^ s ^ "\n");

    fun file_print f =
        (Loop.loopFile f Loop.show)
        handle Parse.Error s => print ("Parse error: " ^ s ^ "\n");

    fun file_type f =
        (Loop.loopFile f (Loop.check Loop.show))
        handle Parse.Error s => print ("Parse error: " ^ s ^ "\n");

    fun file_eval  f =
        (Loop.loopFile f (Loop.eval Loop.show)) 
        handle Parse.Error s => print ("Parse error: " ^ s ^ "\n");
    
    fun file f =
        (Loop.loopFile f (Loop.usual Loop.show)) 
        handle Parse.Error s => print ("Parse error: " ^ s ^ "\n");

end
