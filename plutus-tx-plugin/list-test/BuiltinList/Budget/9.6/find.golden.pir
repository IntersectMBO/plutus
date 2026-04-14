let
  data (Tuple2 :: * -> * -> *) a b | Tuple2_match where
    Tuple2 : a -> b -> Tuple2 a b
  data (Maybe :: * -> *) a | Maybe_match where
    Just : a -> Maybe a
    Nothing : Maybe a
  !find : all a. (a -> bool) -> list a -> Maybe a
    = /\a ->
        \(p : a -> bool) ->
          letrec
            !go : list a -> Maybe a
              = (let
                    r = Maybe a
                  in
                  \(z : r) (f : a -> list a -> r) (xs : list a) ->
                    case r xs [f, z])
                  (Nothing {a})
                  (\(x : a) (xs : list a) ->
                     case
                       (all dead. Maybe a)
                       (p x)
                       [(/\dead -> go xs), (/\dead -> Just {a} x)]
                       {all dead. dead})
          in
          go
in
\(xs : list integer) ->
  Tuple2
    {Maybe integer}
    {Maybe integer}
    (find
       {integer}
       (\(v : integer) -> case bool (lessThanInteger v 8) [True, False])
       xs)
    (find
       {integer}
       (\(v : integer) -> case bool (lessThanInteger v 12) [True, False])
       xs)