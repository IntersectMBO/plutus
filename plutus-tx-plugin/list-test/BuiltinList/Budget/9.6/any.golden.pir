let
  data (Tuple2 :: * -> * -> *) a b | Tuple2_match where
    Tuple2 : a -> b -> Tuple2 a b
  !any : all a. (a -> bool) -> list a -> bool
    = /\a ->
        \(p : a -> bool) ->
          letrec
            !go : list a -> bool
              = \(xs : list a) ->
                  case
                    bool
                    xs
                    [ (\(x : a) (xs : list a) ->
                         case
                           (all dead. bool)
                           (p x)
                           [(/\dead -> go xs), (/\dead -> True)]
                           {all dead. dead})
                    , False ]
          in
          go
in
\(xs : list integer) ->
  Tuple2
    {bool}
    {bool}
    (any
       {integer}
       (\(v : integer) -> case bool (lessThanInteger v 8) [True, False])
       xs)
    (any
       {integer}
       (\(v : integer) -> case bool (lessThanInteger v 12) [True, False])
       xs)