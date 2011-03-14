(* Chris Okasaki / Robert Harper
   School of Computer Science
   Carnegie Mellon University
   Pittsburgh, PA 15213
   cokasaki@cs.cmu.edu *)

signature INPUT =
sig

  val readfile  : string -> char Stream.stream
  val readkeybd : unit   -> char Stream.stream

  val promptkeybd : string -> char Stream.stream
end

structure Input :> INPUT =
struct

  structure T = TextIO
  structure S = Stream

  fun scons (l, s) = S.delay (fn () => S.Cons(l, s))

  fun getchars file close =
      let fun get () : char S.stream =
          if T.endOfStream file then
              (close (); S.empty)
          else
              doline (explode (valOf (T.inputLine file)))
            
          and doline cs = foldr scons ( S.delay (fn () => S.force (get ())) ) cs
              
      in S.delay (fn () => S.force (get ())) end

  fun readfile filename =
      let val file = T.openIn filename
      in
          getchars file (fn () => T.closeIn file)
      end

  fun readkeybd () = getchars T.stdIn (fn () => ())

  fun promptkeybd prompt =
      let fun get () =
          (T.output (T.stdOut, prompt);
           T.flushOut T.stdOut;
           if T.endOfStream T.stdIn
               then S.empty
           else doline (explode (valOf (T.inputLine T.stdIn))))
          and doline cs = foldr scons ( S.delay (fn () => S.force (get ())) ) cs
      in 
          S.delay (fn () => S.force (get ()))
      end

end
