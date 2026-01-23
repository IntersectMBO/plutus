let
  data (Tuple2 :: * -> * -> *) a b | Tuple2_match where
    Tuple2 : a -> b -> Tuple2 a b
in
\(xs : list integer) ->
  (let
      r = Tuple2 integer (list integer)
    in
    \(f : integer -> list integer -> r) (xs : list integer) -> case r xs [f])
    (\(ds : integer) (ds : list integer) ->
       Tuple2 {integer} {list integer} ds ds)
    xs