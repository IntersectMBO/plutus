let
  data (Tuple :: * -> * -> *) a b | Tuple_match where
    Tuple2 : a -> b -> Tuple a b
in
\(xs : list integer) ->
  (let
      r = Tuple integer (list integer)
    in
    \(f : integer -> list integer -> r) (xs : list integer) -> case r xs [f])
    (\(ds : integer) (ds : list integer) ->
       Tuple2 {integer} {list integer} ds ds)
    xs