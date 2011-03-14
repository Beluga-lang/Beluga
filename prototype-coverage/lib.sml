signature LIB = sig
  
  (* separate
   * Example: separate ";" Int.toString [3,4,5]  =  "3;4;5"
   *)
  val separate : string -> ('a -> string) -> 'a list -> string

  (* combine [[x11, ..., x1n], ..., [xm1, ..., xmn]] =
   *   list of all possible lists formed by taking one element from [x11, ..., x1n],
   *    then one element from [x21, ..., x2n],
   *    ...
   *    and finally one element from [xm1, ..., xmn].
   *
   *  Example:  combine [[1, 2, 3], [100], [888, 999]]
   *               = [[1, 100, 888], [1, 100, 999], [2, 100, 888], [2, 100, 999],
   *                  [3, 100, 888], [3, 100, 999]]
   *
   *  Example:  combine [["a"], ["b"], ["c"]] = [["a"], ["b"], ["c"]]
   *)
  val combine : 'a list list -> 'a list list

  (* foldNonempty f xs
   * applies the binary function f ``between'' every element of xs:
   * 
   * foldNonempty (op+) [1, 6, 100]  =  107
   *
   * Differences from foldl/foldr: foldNonempty doesn't work on an empty list,
   *   and if passed with a singleton list, it returns that element (instead of applying
   *   the binary function to that element and the identity; foldNonempty doesn't even
   *   take an identity).
   *)
  val foldNonempty : ('a * 'a -> 'a) -> 'a list -> 'a
end


structure Lib :> LIB = struct

  fun separate separator f [] = ""
    | separate separator f [x] = f(x)
    | separate separator f (x1::xs) = f(x1) ^ separator ^ separate separator f xs

  fun combine ([] : 'a list list) = ([] : 'a list list)
    | combine [list] = List.map (fn x => [x]) list
    | combine (firstList::rest) =
        let val restCombinations : 'a list list = combine rest
            fun addToCombination elem combination =  (elem::combination)
            fun combineWith elem =
              List.map (addToCombination elem) restCombinations
        in
          List.concat (List.map combineWith firstList)
        end

  fun foldNonempty f xs =
    let val last::revxs = List.rev xs
    in
      List.foldl f last revxs 
    end

end
