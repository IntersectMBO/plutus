let
  data (Tuple2 :: * -> * -> *) a b | Tuple2_match where
    Tuple2 : a -> b -> Tuple2 a b
  !elem : all a. (\a -> a -> a -> bool) a -> a -> list a -> bool
    = /\a ->
        \(`$dEq` : (\a -> a -> a -> bool) a) (a : a) ->
          letrec
            !go : list a -> bool
              = \(xs : list a) ->
                  case
                    bool
                    xs
                    [ (\(x : a) (xs : list a) ->
                         case
                           (all dead. bool)
                           (`$dEq` a x)
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
    (elem {integer} (\(x : integer) (y : integer) -> equalsInteger x y) 8 xs)
    (elem {integer} (\(x : integer) (y : integer) -> equalsInteger x y) 12 xs)