let
  data Unit | Unit_match where
    Unit : Unit
in
letrec
  !last : all a. list a -> a
    = /\a ->
        \(eta : list a) ->
          case
            (Unit -> a)
            eta
            [ (\(x : a) (xs : list a) (ds : Unit) ->
                 case a xs [(\(ds : a) (ds : list a) -> last {a} xs), x])
            , (\(ds : Unit) ->
                 let
                   !x : Unit = trace {Unit} "PT25" Unit
                 in
                 error {a}) ]
            Unit
in
\(xs : list integer) -> last {integer} xs