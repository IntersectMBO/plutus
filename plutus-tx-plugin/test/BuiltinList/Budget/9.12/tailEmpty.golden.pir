let
  data Unit | Unit_match where
    Unit : Unit
in
\(ds : list integer) ->
  (let
      r = Unit -> list integer
    in
    \(z : r) (f : integer -> list integer -> r) (xs : list integer) ->
      case r xs [f, z])
    (\(ds : Unit) ->
       let
         !x : Unit = trace {Unit} "PT25" Unit
       in
       error {list integer})
    (\(x : integer) (xs : list integer) (ds : Unit) -> xs)
    []
    Unit