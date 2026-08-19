let
  data Unit | Unit_match where
    Unit : Unit
in
\(xs : list integer) ->
  let
    !l : list integer = dropList {integer} 5 xs
  in
  (let
      r = Unit -> Unit -> integer
    in
    \(z : r) (f : integer -> list integer -> r) (xs : list integer) ->
      case r xs [f, z])
    (\(_ann : Unit) ->
       let
         !x : Unit = trace {Unit} "PT22" Unit
       in
       error {Unit -> integer})
    (\(x : integer) (xs : list integer) (ds : Unit) (_ann : Unit) -> x)
    l
    Unit
    Unit