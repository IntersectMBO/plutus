let
  data (Tuple2 :: * -> * -> *) a b | Tuple2_match where
    Tuple2 : a -> b -> Tuple2 a b
  data (Maybe :: * -> *) a | Maybe_match where
    Just : a -> Maybe a
    Nothing : Maybe a
in
\(ds : list integer) ->
  (let
      r = Maybe (Tuple2 integer (list integer))
    in
    \(z : r) (f : integer -> list integer -> r) (xs : list integer) ->
      case r xs [f, z])
    (Nothing {Tuple2 integer (list integer)})
    (\(h : integer) (t : list integer) ->
       Just
         {Tuple2 integer (list integer)}
         (Tuple2 {integer} {list integer} h t))
    []