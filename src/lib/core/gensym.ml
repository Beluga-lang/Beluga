(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(* Given an alphabet of strings as an array, creates a symbol
   generator over the alphabet *)
let create_symbols (alphabet : string array) : string Stream.t =
  let next i =
    let length = Array.length alphabet in
    let symbol = Array.get alphabet (i mod length)
    and suffix =
      if i < length then ""
      else string_of_int (i / length)
    in
        (* '%' is a special character denoting a generated symbol.
           This symbol is normally unparsable---the only way to create
           such a name is through gensym.  Thus gensym should always
           generate a unique symbol. *)
(*      then Some (symbol          ^ "%")
      else Some (symbol ^ suffix ^ "%") *)
      Some (symbol ^ suffix ) 
  in
    Stream.from next



module type GENSYM = sig

  val gensym : unit -> string
  val name_gensym: string -> (unit -> string)
  val reset : unit -> unit

end



module VarData : GENSYM = struct

  let create () = create_symbols [|
(*   "a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"; "i"; "j"; "k"; "l"; "m";
      "n"; "o"; "p"; "q"; "r"; "s"; "t"; "u"; "v"; "w";*) 
     "y"; "x"; "z"  |]

  let symbols = ref (create ())

  let gensym () = Stream.next !symbols

  let name_gensym s = 
    let symbols = create_symbols [| s |] in 
      (fun () -> Stream.next symbols)

  let reset () = (symbols := create ())
end


module MVarData : GENSYM = struct

  let create () = create_symbols [|
    (*  "A"; "B"; "C"; "D"; "E"; "F"; "G"; "H"; "I" ; "J"; "K"; "L"; "M";
         "N"; "O"; "P"; "Q"; "R" ; "S"; "T"; "U"; "V"; "W"; *)
         "Y"; "X"; "Z"        |]

  let symbols = ref (create ())
  
  let gensym () = Stream.next !symbols
  
  let name_gensym s = 
    let symbols = create_symbols [| s |] in 
      (fun () -> Stream.next symbols)

  let reset () = (symbols := create ())
end


let reset () =
  VarData.reset()
; MVarData.reset()
