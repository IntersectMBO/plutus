let
  data (Maybe :: * -> *) a | Maybe_match where
    Just : a -> Maybe a
    Nothing : Maybe a
  data (Tuple :: * -> * -> *) a b | Tuple_match where
    Tuple2 : a -> b -> Tuple a b
in
\(ds : list integer) ->
  (let
      r = Maybe (Tuple integer (list integer))
    in
    \(z : r) (f : integer -> list integer -> r) (xs : list integer) ->
      case r xs [f, z])
    (Nothing {Tuple integer (list integer)})
    (\(h : integer) (t : list integer) ->
       Just
         {Tuple integer (list integer)}
         (Tuple2 {integer} {list integer} h t))
    []