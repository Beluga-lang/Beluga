include Stdlib.Option

module M = Monad.Make (struct
  type nonrec 'a t = 'a t

  let return = some

  let bind f x = bind x f
end)

include (M : Monad.MONAD with type 'a t := 'a t)

include (Functor.Make (M) : Functor.FUNCTOR with type 'a t := 'a t)

include (Apply.Make (M) : Apply.APPLY with type 'a t := 'a t)

let eliminate default f = function
  | None -> default ()
  | Some x -> f x

let get' e o = eliminate (Misc.throw e) Fun.id o

let get_or_else default = eliminate default Fun.id

let of_bool = function
  | true -> some ()
  | false -> none

let from_predicate p a = if p a then some a else none

let empty = none

let lazy_alt p q =
  lazy
    (let p = Lazy.force p in
     match p with
     | Some _ -> p
     | None -> Lazy.force q)

let ( <||> ) = lazy_alt

let alt o1 o2 =
  match (o1, o2) with
  | Some x, _ -> Some x
  | _, Some y -> Some y
  | _ -> None

let ( <|> ) = alt

let void o = o $> Fun.const ()

let when_some l f = eliminate (Fun.const ()) f l

let print ppv ppf = function
  | None -> ()
  | Some v -> Format.fprintf ppf "%a" ppv v

let pp ppv ppf = function
  | None -> Format.fprintf ppf "None"
  | Some v -> Format.fprintf ppf "Some (@[%a@])" ppv v

module MakeEq (E : Eq.EQ) : Eq.EQ with type t = E.t t = Eq.Make (struct
  type nonrec t = E.t t

  let equal = equal E.equal
end)

module MakeOrd (O : Ord.ORD) : Ord.ORD with type t = O.t t = Ord.Make (struct
  type nonrec t = O.t t

  let compare = compare O.compare
end)

module MakeShow (S : Show.SHOW) : Show.SHOW with type t = S.t t =
Show.Make (struct
  type nonrec t = S.t t

  let pp = pp S.pp
end)
