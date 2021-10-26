include Stdlib.Option

let (<|>) o1 o2 = fold ~none:o2 ~some o1
