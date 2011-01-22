signature ENV = sig
  type name = MinML.name
  type env
  datatype object =
           Exp of MinML.exp
         | Closure of MinML.exp * env
                      
  val empty : env
              
  val lookup : env -> name -> object
  val extend : env -> name * object -> env
  val extend_list : env -> (name * object) list -> env

  val extend_rec : env -> name * object -> env   (* Extend, creating a cycle *)
                                           
  val toString : env -> string
                        
  exception NotFound
end

structure Env :> ENV = struct
  structure M = MinML

  type name = M.name

  datatype env = Env of (name * object') list
       and object' = Exp' of M.exp
                   | Closure' of M.exp * (env option ref)
                                  
  datatype object =
           Exp of MinML.exp
         | Closure of MinML.exp * env

  val empty = Env []

  fun lift f env = f (Option.valOf (!env))

  fun str trail (Env list) =
      Lib.separate ", "
                   (fn (x, obj) =>
                       "\"" ^ x ^ "\" |-> " ^
                       (case obj of
                          Exp' exp => Print.expToString exp
                        | Closure' (exp, env) =>
                          (if List.exists (fn r => r = env) trail then "*"
                           else "(" ^ Print.expToString exp ^ " | " ^ lift (str (env::trail)) env ^ ")")))
                   list

  fun toString env = str [] env

  excepption NotFound
  fun assoc orig x [] =
      (print ("Env.assoc: \"" ^ x ^ "\" not found in " ^ toString (Env orig)); raise NotFound)
    | assoc orig x ((y, r)::rest) = if x = y then r else assoc orig x rest

  fun lookup (Env list) x =
      let val obj = assoc list x list
      in
        case obj of
          Exp' exp => Exp exp
        | Closure' (exp, envref) => Closure (exp, Option.valOf (!envref))
      end

  fun extend (Env list) (x, obj) =
      let val obj' = case obj of Exp exp => Exp' exp
                               | Closure (exp, env) => Closure' (exp, ref (SOME env))
      in
        Env((x, obj')::list)
      end

  fun extend_rec (Env list) (x, Closure(exp, env)) =
      let val hole = ref NONE
          val env = Env((x, Closure'(exp, hole)) :: list)
          val _ = hole := SOME env
      in
        env
      end

  fun extend_list env [] = env
    | extend_list env ((x, v):: rest) = extend_list (extend env (x, v)) rest

end
