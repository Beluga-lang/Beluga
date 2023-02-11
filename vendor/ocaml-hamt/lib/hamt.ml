module BitUtils : sig
  (* Given a bitmap, counts the number of one-bits *)
  val ctpop : int -> int

  (* Given a bitmap and a subhash, returns the index into the list *)
  val from_bitmap : int -> int -> int

  (** Given a bitmap and an integer, returns the boolean corresponding to the
      n-th bit (0 is the weakest) of the bitmap *)
  val nth_bit_set : int -> int -> bool

  (** Given a list of indices, returns the bitmap with one-bits at these
      indices *)
  val indices_to_bitmap : int list -> int

  (* Given a bitmap, returns the list of indices where a one-bit is
     present *)
  val bitmap_to_indices : int -> int list
end = struct
  let sk5 = 0x55555555

  let sk3 = 0x33333333

  let skf0 = 0xf0f0f0f

  let[@inline] ctpop map =
    let map = map - ((map lsr 1) land sk5) in
    let map = (map land sk3) + ((map lsr 2) land sk3) in
    let map = (map land skf0) + ((map lsr 4) land skf0) in
    let map = map + (map lsr 8) in
    (map + (map lsr 16)) land 0x3f

  let[@inline] from_bitmap bitmap sub_hash =
    let mask = pred (1 lsl sub_hash) in
    ctpop (bitmap land mask)

  let bitmap_to_indices =
    let rec loop ix bitmap =
      if bitmap = 0 then []
      else if ix = 32 then []
      else if bitmap land 1 = 0 then loop (succ ix) (bitmap asr 1)
      else ix :: loop (succ ix) (bitmap asr 1)
    in
    fun bitmap -> loop 0 bitmap

  let[@inline] indices_to_bitmap l =
    List.fold_left (fun x i -> x lor (1 lsl i)) 0 l

  let[@inline] nth_bit_set bitmap n = (bitmap asr n) land 1 = 1
end

open BitUtils

module type CONFIG = sig
  (* Number of bits taken from the hashed key at every step *)
  val shift_step : int

  (* Maximum size of a BitmapIndexedNode*)
  val bmnode_max : int

  (* Minimum size of an ArrayNode (must be lesser than bmnode_max) *)
  val arrnode_min : int
end

module StdConfig : CONFIG = struct
  let shift_step = 5

  let bmnode_max = 16

  let arrnode_min = 8
end

module StdConfig32 : CONFIG = struct
  let shift_step = 4

  let bmnode_max = 8

  let arrnode_min = 4
end

module type S = sig
  type key

  type 'a t

  val empty : 'a t

  val is_empty : 'a t -> bool

  val singleton : key -> 'a -> 'a t

  val cardinal : 'a t -> int

  val length : 'a t -> int

  val update : key -> ('a option -> 'a option) -> 'a t -> 'a t

  val add : key -> 'a -> 'a t -> 'a t

  val add_carry : key -> 'a -> 'a t -> 'a t * 'a option

  val remove : key -> 'a t -> 'a t

  val extract : key -> 'a t -> 'a * 'a t

  val alter : key -> ('a -> 'a option) -> 'a t -> 'a t

  val modify : key -> ('a -> 'a) -> 'a t -> 'a t

  val modify_def : 'a -> key -> ('a -> 'a) -> 'a t -> 'a t

  val find : key -> 'a t -> 'a

  val find_opt : key -> 'a t -> 'a option

  val mem : key -> 'a t -> bool

  val choose : 'a t -> key * 'a

  val choose_opt : 'a t -> (key * 'a) option

  val pop : 'a t -> (key * 'a) * 'a t

  val keys : 'a t -> key list

  val values : 'a t -> 'a list

  val bindings : 'a t -> (key * 'a) list

  val to_seq : 'a t -> (key * 'a) Seq.t

  val of_seq : (key * 'a) Seq.t -> 'a t

  val iter : (key -> 'a -> unit) -> 'a t -> unit

  val map : ('a -> 'b) -> 'a t -> 'b t

  val mapi : (key -> 'a -> 'b) -> 'a t -> 'b t

  val filterv : ('a -> bool) -> 'a t -> 'a t

  val filter : (key -> 'a -> bool) -> 'a t -> 'a t

  val filter_map : (key -> 'a -> 'b option) -> 'a t -> 'b t

  val foldv : ('a -> 'b -> 'b) -> 'a t -> 'b -> 'b

  val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b

  val for_all : (key -> 'a -> bool) -> 'a t -> bool

  val exists : (key -> 'a -> bool) -> 'a t -> bool

  val partition : (key -> 'a -> bool) -> 'a t -> 'a t * 'a t

  val intersecti : (key -> 'a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t

  val intersect : ('a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t

  val merge :
    (key -> 'a option -> 'b option -> 'c option) -> 'a t -> 'b t -> 'c t

  val union : (key -> 'a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t

  module Import : sig
    module type FOLDABLE = sig
      type key

      type 'a t

      val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
    end

    module Make (M : FOLDABLE with type key = key) : sig
      val add_from : 'a M.t -> 'a t -> 'a t

      val from : 'a M.t -> 'a t
    end

    module AssocList : sig
      val add_from : (key * 'a) list -> 'a t -> 'a t

      val from : (key * 'a) list -> 'a t
    end
  end

  module ExceptionLess : sig
    val extract : key -> 'a t -> 'a option * 'a t

    val alter : key -> ('a -> 'a option) -> 'a t -> 'a t

    val modify : key -> ('a -> 'a) -> 'a t -> 'a t

    val find : key -> 'a t -> 'a option

    val choose : 'a t -> (key * 'a) option
  end
end

module Make (Config : CONFIG) (Key : Hashtbl.HashedType) :
  S with type key = Key.t = struct
  open Config

  (* Branching factor of the structure *)
  let chunk = 1 lsl shift_step

  (* Mask of shift_step `1` bits *)
  let mask = pred chunk

  type key = Key.t

  let hash = Key.hash

  type 'a t =
    | Empty
    | Leaf of int * key * 'a
    | HashCollision of int * (key * 'a) list
    | BitmapIndexedNode of int * 'a t array
    | ArrayNode of int * 'a t array

  let empty = Empty

  let[@inline] leaf h k v = Leaf (h, k, v)

  let[@inline] singleton k v = Leaf (hash k, k, v)

  let[@inline] is_empty = function
    | Empty -> true
    | _ -> false

  let rec cardinal = function
    | Empty -> 0
    | Leaf (_, _, _) -> 1
    | HashCollision (_, pairs) -> List.length pairs
    | BitmapIndexedNode (_, base) ->
        Array.fold_left (fun acc child -> acc + cardinal child) 0 base
    | ArrayNode (_, children) ->
        Array.fold_left (fun acc child -> acc + cardinal child) 0 children

  let length = cardinal

  let[@inline] is_tip_node = function
    | Empty
    | Leaf (_, _, _)
    | HashCollision (_, _) ->
        true
    | _ -> false

  let[@inline] hash_fragment shift h = (h asr shift) land mask

  let remove tab ix =
    let tab' = Array.make (Array.length tab - 1) Empty in
    Array.blit tab 0 tab' 0 ix;
    Array.blit tab (succ ix) tab' ix (Array.length tab - ix - 1);
    tab'

  let add_tab tab ix v =
    let tab' = Array.make (Array.length tab + 1) Empty in
    Array.blit tab 0 tab' 0 ix;
    Array.blit tab ix tab' (succ ix) (Array.length tab - ix);
    tab'.(ix) <- v;
    tab'

  let set_tab tab ix v =
    let tab' = Array.copy tab in
    tab'.(ix) <- v;
    tab'

  let rec combine_tip shift node1 node2 =
    match (node1, node2) with
    | Leaf (h1, k1, v1), Leaf (h2, k2, v2) when Int.equal h1 h2 ->
        HashCollision (h1, [ (k1, v1); (k2, v2) ])
    | Leaf (h1, _, _), Leaf (h2, _, _)
    | Leaf (h1, _, _), HashCollision (h2, _) ->
        let sub_h1 = hash_fragment shift h1 in
        let sub_h2 = hash_fragment shift h2 in
        let nodeA, nodeB =
          if sub_h1 < sub_h2 then (node1, node2) else (node2, node1)
        in
        let bitmap = (1 lsl sub_h1) lor (1 lsl sub_h2) in
        BitmapIndexedNode
          ( bitmap
          , if Int.equal sub_h1 sub_h2 then
              [| combine_tip (shift + shift_step) node1 node2 |]
            else [| nodeA; nodeB |] )
    | HashCollision (_, _), Leaf (_, _, _) -> combine_tip shift node2 node1
    | _ -> failwith "combine_tip"

  let rec update_list update k = function
    | [] -> (
        match update None with
        | None -> []
        | Some v -> [ (k, v) ])
    | ((kx, vx) as x) :: xs ->
        if Key.equal kx k then
          match update (Some vx) with
          | None -> xs
          | Some v -> (k, v) :: xs
        else x :: update_list update k xs

  let expand_bitmap_node =
    let rec fill tab sub_nodes ix jx bitmap =
      if Int.equal ix chunk then jx
      else if Int.equal (bitmap land 1) 0 then
        fill tab sub_nodes (succ ix) jx (bitmap asr 1)
      else (
        tab.(ix) <- sub_nodes.(jx);
        fill tab sub_nodes (succ ix) (succ jx) (bitmap asr 1))
    in
    fun sub_hash node bitmap sub_nodes ->
      let tab = Array.make chunk Empty in
      let n = fill tab sub_nodes 0 0 bitmap in
      tab.(sub_hash) <- node;
      ArrayNode (n, tab)

  let pack_array_node =
    let rec loop children to_remove base ix jx bitmap =
      if Int.equal ix chunk then BitmapIndexedNode (bitmap, base)
      else if is_empty children.(ix) || to_remove ix then
        loop children to_remove base (succ ix) jx bitmap
      else (
        base.(jx) <- children.(ix);
        loop children to_remove base (succ ix) (succ jx)
          (bitmap lor (1 lsl ix)))
    in
    fun to_remove nb_children children ->
      let base = Array.make nb_children Empty in
      loop children to_remove base 0 0 0

  let rec reify_node = function
    | Empty -> Empty
    | Leaf (h, k, v) -> Leaf (h, k, v)
    | HashCollision (_, []) -> Empty
    | HashCollision (h, [ (k, v) ]) -> Leaf (h, k, v)
    | HashCollision (h, li) -> HashCollision (h, li)
    | BitmapIndexedNode (bitmap, base) ->
        if Int.equal (Array.length base) 0 then Empty
        else if Int.equal (Array.length base) 1 && is_tip_node base.(0) then
          base.(0)
        else if Array.length base > bmnode_max then failwith "reify_node"
        else BitmapIndexedNode (bitmap, base)
    | ArrayNode (nb_children, children) ->
        if nb_children < arrnode_min then
          reify_node (pack_array_node (fun _ -> false) nb_children children)
        else ArrayNode (nb_children, children)

  let bitmap_to_array bitmap base =
    let children = Array.make chunk Empty
    and n = ref 0 in
    for i = 0 to mask do
      if nth_bit_set bitmap i then (
        children.(i) <- base.(!n);
        incr n)
    done;
    children

  type change =
    | Nil
    | Added
    | Modified
    | Removed

  let[@inline] change old_is_empty new_is_empty =
    if old_is_empty then if new_is_empty then Nil else Added
    else if new_is_empty then Removed
    else Modified

  let rec alter_node ?(mute = false) shift hash key update = function
    | Empty -> (
        match update None with
        | None -> Empty
        | Some s -> leaf hash key s)
    | Leaf (h, k, v) as leaf1 -> (
        if Key.equal k key then
          match update (Some v) with
          | None -> Empty
          | Some s -> leaf h k s
        else
          match update None with
          | None -> leaf1
          | Some x -> combine_tip shift leaf1 (Leaf (hash, key, x)))
    | HashCollision (h, pairs) as hash_collision -> (
        if Int.equal hash h then
          let pairs = update_list update key pairs in
          match pairs with
          | [] -> failwith "alter_node" (* Should never happen *)
          | [ (k, v) ] -> leaf h k v
          | _ -> HashCollision (h, pairs)
        else
          match update None with
          | None -> hash_collision
          | Some x -> combine_tip shift (Leaf (hash, key, x)) hash_collision)
    | BitmapIndexedNode (bitmap, base) as bm_node -> (
        let sub_hash = hash_fragment shift hash in
        let ix = from_bitmap bitmap sub_hash in
        let bit = 1 lsl sub_hash in
        let not_exists = Int.equal (bitmap land bit) 0 in
        let child = if not_exists then Empty else base.(ix) in
        let child =
          alter_node ~mute (shift + shift_step) hash key update child
        in
        match change not_exists (is_empty child) with
        | Nil -> bm_node
        | Modified ->
            if mute then (
              base.(ix) <- child;
              bm_node)
            else BitmapIndexedNode (bitmap, set_tab base ix child)
        | Removed ->
            let bitmap = bitmap land lnot bit in
            if Int.equal bitmap 0 then Empty
            else if
              Int.equal (Array.length base) 2 && is_tip_node base.(ix lxor 1)
            then base.(ix lxor 1)
            else BitmapIndexedNode (bitmap, remove base ix)
        | Added ->
            if Int.equal (Array.length base) bmnode_max then
              expand_bitmap_node sub_hash child bitmap base
            else BitmapIndexedNode (bitmap lor bit, add_tab base ix child))
    | ArrayNode (nb_children, children) as arr_node -> (
        let sub_hash = hash_fragment shift hash in
        let child = children.(sub_hash) in
        let child' =
          alter_node ~mute (shift + shift_step) hash key update child
        in
        match change (is_empty child) (is_empty child') with
        | Nil -> arr_node
        | Added ->
            if mute then (
              children.(sub_hash) <- child';
              ArrayNode (succ nb_children, children))
            else
              ArrayNode (succ nb_children, set_tab children sub_hash child')
        | Modified ->
            if mute then (
              children.(sub_hash) <- child';
              arr_node)
            else ArrayNode (nb_children, set_tab children sub_hash child')
        | Removed ->
            if Int.equal nb_children arrnode_min then
              pack_array_node (Int.equal sub_hash) nb_children children
            else if mute then (
              children.(sub_hash) <- Empty;
              ArrayNode (pred nb_children, children))
            else ArrayNode (pred nb_children, set_tab children sub_hash Empty)
        )

  let rec copy hamt =
    match hamt with
    | Empty
    | Leaf (_, _, _)
    | HashCollision (_, _) ->
        hamt
    | BitmapIndexedNode (bitmap, base) ->
        BitmapIndexedNode (bitmap, Array.map copy base)
    | ArrayNode (nb_children, children) ->
        ArrayNode (nb_children, Array.map copy children)

  let update key update hamt = alter_node 0 (hash key) key update hamt

  let add k v hamt = update k (fun _ -> Some v) hamt

  let add_mute k v hamt =
    alter_node ~mute:true 0 (hash k) k (fun _ -> Some v) hamt

  let add_carry k v hamt =
    let previous_value = ref None in
    let r =
      update k
        (fun v' ->
          previous_value := v';
          Some v)
        hamt
    in
    (r, !previous_value)

  let remove k hamt = update k (fun _ -> None) hamt

  let extract k hamt =
    let value = ref (Obj.magic 0) in
    let r =
      update k
        (function
          | None -> raise Not_found
          | Some v ->
              value := v;
              None)
        hamt
    in
    (!value, r)

  let alter k f hamt =
    update k
      (function
        | None -> raise Not_found
        | Some v -> f v)
      hamt

  let modify k f hamt =
    update k
      (function
        | None -> raise Not_found
        | Some v -> Some (f v))
      hamt

  let modify_def v0 k f hamt =
    update k
      (function
        | None -> Some (f v0)
        | Some v -> Some (f v))
      hamt

  let rec alter_hc f = function
    | [] -> []
    | (k, v) :: xs -> (
        match f k v with
        | None -> alter_hc f xs
        | Some w -> (k, w) :: alter_hc f xs)

  and alter_bmnode =
    let rec aux f base n = function
      | [] -> ([], [])
      | i :: is -> (
          match alter_all f base.(n) with
          | Empty -> aux f base (succ n) is
          | x ->
              let iss, bss = aux f base (succ n) is in
              (i :: iss, x :: bss))
    in
    fun f indices base -> aux f base 0 indices

  and alter_all f = function
    | Empty -> Empty
    | Leaf (h, k, v) -> (
        match f k v with
        | None -> Empty
        | Some x -> leaf h k x)
    | HashCollision (h, pairs) -> (
        match alter_hc f pairs with
        | [] -> Empty
        | [ (k, v) ] -> Leaf (h, k, v)
        | pairs' -> HashCollision (h, pairs'))
    | BitmapIndexedNode (bitmap, base) -> (
        match alter_bmnode f (bitmap_to_indices bitmap) base with
        | _, [] -> Empty
        | _, [ x ] when is_tip_node x -> x
        | indices, base ->
            BitmapIndexedNode (indices_to_bitmap indices, Array.of_list base)
        )
    | ArrayNode (_nb_children, children) ->
        let children = Array.map (alter_all f) children in
        let nb_children =
          Array.fold_left
            (fun n v -> if is_empty v then n else succ n)
            0 children
        in
        if nb_children < arrnode_min then
          pack_array_node (fun _ -> false) nb_children children
        else ArrayNode (nb_children, children)

  let map f hamt = alter_all (fun _k v -> Some (f v)) hamt

  let filter f hamt =
    alter_all (fun k v -> if f k v then Some v else None) hamt

  let filterv f hamt =
    alter_all (fun _k v -> if f v then Some v else None) hamt

  let filter_map f hamt = alter_all f hamt

  let mapi f hamt = alter_all (fun k v -> Some (f k v)) hamt

  let rec iter f = function
    | Empty -> ()
    | Leaf (_, k, v) -> f k v
    | HashCollision (_, pairs) -> List.iter (fun (x, y) -> f x y) pairs
    | BitmapIndexedNode (_, base) -> Array.iter (iter f) base
    | ArrayNode (_, children) -> Array.iter (iter f) children

  let rec assoc k = function
    | [] -> raise Not_found
    | (k', v) :: xs -> if Key.equal k k' then v else assoc k xs

  let rec assoc_notrace k = function
    | [] -> raise_notrace Not_found
    | (k', v) :: xs -> if Key.equal k k' then v else assoc_notrace k xs

  module Notrace = struct
    let find =
      let rec find hash key = function
        | Empty -> raise_notrace Not_found
        | Leaf (_, k, v) ->
            if Key.equal k key then v else raise_notrace Not_found
        | HashCollision (_, pairs) -> assoc_notrace key pairs
        | BitmapIndexedNode (bitmap, base) ->
            let bit =
              let sub_hash = hash land mask in
              1 lsl sub_hash
            in
            if Int.equal (bitmap land bit) 0 then raise_notrace Not_found
            else
              let node =
                let idx = ctpop (bitmap land pred bit) in
                base.(idx)
              in
              find (hash lsr shift_step) key node
        | ArrayNode (_, children) ->
            let child = children.(hash land mask) in
            if is_empty child then raise_notrace Not_found
            else find (hash lsr shift_step) key child
      in
      fun key -> find (hash key) key
  end

  let find key t =
    match Notrace.find key t with
    | x -> x
    | exception Not_found -> raise Not_found

  let find_opt key t =
    match Notrace.find key t with
    | e -> Some e
    | exception Not_found -> None

  let mem key hamt =
    match Notrace.find key hamt with
    | _ -> true
    | exception Not_found -> false

  let rec fold f hamt v0 =
    match hamt with
    | Empty -> v0
    | Leaf (_, k, v) -> f k v v0
    | HashCollision (_, pairs) ->
        List.fold_right (fun (k, v) acc -> f k v acc) pairs v0
    | BitmapIndexedNode (_, base) -> Array.fold_right (fold f) base v0
    | ArrayNode (_, children) -> Array.fold_right (fold f) children v0

  let foldv f hamt v0 = fold (fun _k v acc -> f v acc) hamt v0

  let bindings hamt = fold (fun k v acc -> (k, v) :: acc) hamt []

  let to_seq =
    let rec to_seq = function
      | Empty -> Seq.empty
      | Leaf (_, k, v) -> fun () -> Seq.Cons ((k, v), Seq.empty)
      | HashCollision (_, list) -> List.to_seq list
      | ArrayNode (_, arr)
      | BitmapIndexedNode (_, arr) ->
          Seq.flat_map to_seq (Array.to_seq arr)
    in
    to_seq

  let of_seq =
    let rec loop seq acc =
      match seq () with
      | Seq.Nil -> acc
      | Seq.Cons ((k, v), seq) ->
          let acc = add_mute k v acc in
          loop seq acc
    in
    fun seq -> loop seq empty

  let keys hamt = fold (fun k _v acc -> k :: acc) hamt []

  let values hamt = fold (fun _k v acc -> v :: acc) hamt []

  let for_all f hamt =
    match iter (fun k v -> if not (f k v) then raise_notrace Exit) hamt with
    | () -> true
    | exception Exit -> false

  let exists f hamt =
    match iter (fun k v -> if f k v then raise_notrace Exit) hamt with
    | () -> false
    | exception Exit -> true

  let partition f hamt =
    fold
      (fun k v (yes, no) ->
        if f k v then (add k v yes, no) else (yes, add k v no))
      hamt (Empty, Empty)

  let choose =
    let rec choose = function
      | Empty -> raise Not_found
      | Leaf (_, k, v) -> (k, v)
      | HashCollision (_, li) -> List.hd li
      | BitmapIndexedNode (_, base) -> choose base.(0)
      | ArrayNode (_, children) -> choose (find_non_empty_child children 0)
    and find_non_empty_child children n =
      if is_empty children.(n) then find_non_empty_child children (succ n)
      else children.(n)
    in
    choose

  let choose_opt t =
    match choose t with
    | exception Not_found -> None
    | x -> Some x

  let pop hamt =
    let k, v = choose hamt in
    ((k, v), remove k hamt)

  let rec intersect_array :
            'a 'b.
               int
            -> (key -> 'a -> 'b -> 'c)
            -> 'a t array
            -> 'b t array
            -> 'c t =
   fun shift f children1 children2 ->
    let children = Array.make chunk Empty
    and nb_children = ref 0 in
    for i = 0 to mask do
      let child = intersect_node shift f children1.(i) children2.(i) in
      if child <> Empty then (
        incr nb_children;
        children.(i) <- child)
    done;
    reify_node (ArrayNode (!nb_children, children))

  and intersect_node :
        'a 'b. int -> (key -> 'a -> 'b -> 'c) -> 'a t -> 'b t -> 'c t =
   fun shift f t1 t2 ->
    match (t1, t2) with
    | Empty, _ -> Empty
    | Leaf (h, k, v), _ -> (
        match Notrace.find k t2 with
        | exception Not_found -> Empty
        | v' -> Leaf (h, k, f k v v'))
    | HashCollision (h1, li1), HashCollision (h2, li2) ->
        if h1 <> h2 then Empty
        else
          reify_node
            (HashCollision
               ( h1
               , List.fold_left
                   (fun acc (k, v) ->
                     match assoc_notrace k li2 with
                     | exception Not_found -> acc
                     | v' -> (k, f k v v') :: acc)
                   [] li1 ))
    | HashCollision (h, _li), BitmapIndexedNode (bitmap, base) ->
        let bit = 1 lsl hash_fragment shift h in
        if Int.equal (bitmap land bit) 0 then Empty
        else
          let n = ctpop (bitmap land pred bit) in
          let node = intersect_node (shift + shift_step) f t1 base.(n) in
          reify_node (BitmapIndexedNode (bit, [| node |]))
    | HashCollision (h, _li), ArrayNode (_nb_children, children) ->
        let fragment = hash_fragment shift h in
        let child =
          intersect_node (shift + shift_step) f t1 children.(fragment)
        in
        reify_node (BitmapIndexedNode (1 lsl fragment, [| child |]))
    | BitmapIndexedNode (bitmap1, base1), BitmapIndexedNode (bitmap2, base2)
      ->
        let bitmap = bitmap1 land bitmap2 in
        if Int.equal bitmap 0 then Empty
        else
          intersect_array (shift + shift_step) f
            (bitmap_to_array bitmap1 base1)
            (bitmap_to_array bitmap2 base2)
    | BitmapIndexedNode (bitmap, base), ArrayNode (_, children) ->
        intersect_array (shift + shift_step) f
          (bitmap_to_array bitmap base)
          children
    | ArrayNode (_, children1), ArrayNode (_, children2) ->
        intersect_array (shift + shift_step) f children1 children2
    | _, _ -> intersect_node shift (fun k x y -> f k y x) t2 t1

  let intersecti f t1 t2 = intersect_node 0 f t1 t2

  let intersect f t1 t2 = intersecti (fun _ v -> f v) t1 t2

  let rec merge_array :
            'a 'b.
               int
            -> (key -> 'a option -> 'b option -> 'c option)
            -> 'a t array
            -> 'b t array
            -> 'c t =
   fun shift f children1 children2 ->
    let nb_children = ref 0
    and children = Array.make chunk Empty in
    for i = 0 to mask do
      let node = merge_node shift f children1.(i) children2.(i) in
      if node <> Empty then incr nb_children;
      children.(i) <- node
    done;
    reify_node (ArrayNode (!nb_children, children))

  and merge_node :
        'a 'b.
           int
        -> (key -> 'a option -> 'b option -> 'c option)
        -> 'a t
        -> 'b t
        -> 'c t =
   fun shift f t1 t2 ->
    match (t1, t2) with
    | Empty, _ -> alter_all (fun k v -> f k None (Some v)) t2
    | Leaf (h, k, v), _ ->
        let flag = ref false in
        let t2 =
          alter_all
            (fun k' v' ->
              if Key.equal k' k then (
                flag := true;
                f k (Some v) (Some v'))
              else f k' None (Some v'))
            t2
        in
        if !flag then t2
        else alter_node shift h k (fun _ -> f k (Some v) None) t2
    | HashCollision (_, li), _ ->
        let absents = ref li in
        let t2 =
          alter_all
            (fun k' v' ->
              match assoc k' li with
              | exception Not_found -> f k' None (Some v')
              | v ->
                  absents := List.remove_assoc k' !absents;
                  f k' (Some v) (Some v'))
            t2
        in
        List.fold_left
          (fun acc (k, v) ->
            alter_node shift (hash k) k (fun _ -> f k (Some v) None) acc)
          t2 !absents
    | BitmapIndexedNode (bitmap1, base1), BitmapIndexedNode (bitmap2, base2)
      ->
        merge_array shift f
          (bitmap_to_array bitmap1 base1)
          (bitmap_to_array bitmap2 base2)
    | BitmapIndexedNode (bitmap, base), ArrayNode (_, children) ->
        merge_array shift f (bitmap_to_array bitmap base) children
    | ArrayNode (_, children1), ArrayNode (_, children2) ->
        merge_array shift f children1 children2
    | _, _ -> merge_node shift (fun k x y -> f k y x) t2 t1

  let merge f t1 t2 = merge_node 0 f t1 t2

  let union f t1 t2 =
    merge
      (fun k x y ->
        match (x, y) with
        | None, _ -> y
        | _, None -> x
        | Some v1, Some v2 -> f k v1 v2)
      t1 t2

  module Import = struct
    module type FOLDABLE = sig
      type key

      type 'v t

      val fold : (key -> 'v -> 'a -> 'a) -> 'v t -> 'a -> 'a
    end

    module Make (M : FOLDABLE with type key = key) = struct
      let add_from x hamt = M.fold add_mute x (copy hamt)

      let from x = add_from x Empty
    end

    module AssocList = struct
      let add_from assoc hamt =
        List.fold_left (fun acc (k, v) -> add_mute k v acc) (copy hamt) assoc

      let from assoc = add_from assoc Empty
    end
  end

  module ExceptionLess = struct
    let extract k hamt =
      match extract k hamt with
      | v, r -> (Some v, r)
      | exception Not_found -> (None, hamt)

    let alter k f hamt =
      try alter k f hamt with
      | Not_found -> hamt

    let modify k f hamt =
      try modify k f hamt with
      | Not_found -> hamt

    let find k hamt = find_opt k hamt

    let choose hamt =
      try Some (choose hamt) with
      | Not_found -> None
  end
end

module Make' = Make (StdConfig)
