let
  data (Tuple2 :: * -> * -> *) a b | Tuple2_match where
    Tuple2 : a -> b -> Tuple2 a b
  !all : all a. (a -> bool) -> list a -> bool
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
                           [(/\dead -> False), (/\dead -> go xs)]
                           {all dead. dead})
                    , True ]
          in
          go
in
\(xs : list integer) ->
  Tuple2
    {bool}
    {bool}
    (all {integer} (\(v : integer) -> lessThanEqualsInteger 8 v) xs)
    (all {integer} (\(v : integer) -> lessThanEqualsInteger 0 v) xs)