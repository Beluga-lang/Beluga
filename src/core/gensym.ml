(* The stuff in this module is ultimately just a very elaborate way of
   generating the same thing over and over again, esp. the name_gensym
   family of functions.

   Perhaps a name generation should be centralized in Store?
   -je
 *)

(* Given an alphabet of strings as an array, creates a symbol
   generator over the alphabet *)
let create_symbols (alphabet : string array) : string Stream.t =
  let next i =
    let length = Array.length alphabet in
    let symbol = Array.get alphabet (i mod length)
    and suffix =
      if i < length
      then ""
      else string_of_int (i / length)
    in
    (* The below comment is interesting.
       It looks like once upon a time, gensym was used ONLY for
       debugging, since it would generate unparseable names.
       I personally like the idea of distinguishing between names that
       could ostensibly get printed to the user at some point versus
       names that are purely internal, perhaps with some way of
       converting from the latter to the former by analyzing the
       context in which they are being printed and what they are
       supposed to represent in order to cook up a decent name.
       -je
     *)
    (* '%' is a special character denoting a generated symbol.
       This symbol is normally unparsable---the only way to create
       such a name is through gensym.  Thus gensym should always
       generate a unique symbol. *)
    (* then Some (symbol ^ "%")
       else Some (symbol ^ suffix ^ "%") *)
    Some (symbol ^ suffix)
  in
  Stream.from next

module type GENSYM = sig
  val gensym : unit -> string
  val name_gensym: string -> (unit -> string)
  val reset : unit -> unit
end

module VarData : GENSYM = struct
  let create () =
    create_symbols
      [|
        (* "a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"; "i"; "j"; "k"; "l"; "m";
           "n"; "o"; "p"; "q"; "r"; "s"; "t"; "u"; "v"; "w";*)
        "y"; "x"; "z"
      |]

  let symbols = ref (create ())

  let gensym () = Stream.next !symbols

  let name_gensym s =
    let symbols = create_symbols [| s |] in
    (fun () -> Stream.next symbols)

  let reset () =
    symbols := create ()
end


module MVarData : GENSYM = struct
  let create () =
    create_symbols
      [|
        (* "A"; "B"; "C"; "D"; "E"; "F"; "G"; "H"; "I" ; "J"; "K"; "L"; "M";
           "N"; "O"; "P"; "Q"; "R" ; "S"; "T"; "U"; "V"; "W"; *)
        "Y"; "X"; "Z"
      |]

  let symbols = ref (create ())

  let gensym () = Stream.next !symbols

  let name_gensym s =
    let symbols = create_symbols [| s |] in
    (fun () -> Stream.next symbols)

  let reset () =
    symbols := create ()
end


let reset () =
  VarData.reset ();
  MVarData.reset ()
