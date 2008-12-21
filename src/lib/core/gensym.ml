(* -*- coding: utf-8; indent-tabs-mode: nil; -*- *)

(* Given an alphabet of strings as an array, creates a symbol
   generator over the alphabet *)
let create_symbols (alphabet : string array) : string Stream.t =
  let next i =
    let length = Array.length alphabet in
    let symbol = Array.get alphabet (i mod length)
    and suffix = string_of_int      (i /   length) in
      if i < length
        (* '%' is a special character denoting a generated symbol.
           This symbol is normally unparsable – the only way to create
           such a name is through gensym.  Thus gensym should always
           generate a unique symbol. *)
      then Some (symbol          ^ "%")
      else Some (symbol ^ suffix ^ "%")
  in
    Stream.from next



module type GENSYM = sig

  val gensym : unit -> string

end



module VarData : GENSYM = struct

  let symbols = create_symbols [|
                                  "a"; "b"; "c"; "d"; "e"; "f"; "g"; "h"; "i"
                                ; "j"; "k"; "l"; "m"; "n"; "o"; "p"; "q"; "r"
                                ; "s"; "t"; "u"; "v"; "w"; "y"; "x"; "z"
                               |]

  let gensym () = Stream.next symbols

end
