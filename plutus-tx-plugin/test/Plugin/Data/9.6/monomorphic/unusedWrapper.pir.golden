let
  data (Tuple2 :: * -> * -> *) a b | Tuple2_match where
    Tuple2 : a -> b -> Tuple2 a b
  data T | T_match where
    MkT : Tuple2 integer integer -> T
  ~`$WMkT` : Tuple2 integer integer -> T
    = \(conrep : Tuple2 integer integer) ->
        let
          !conrep : Tuple2 integer integer = conrep
        in
        MkT conrep
  ~mkT : Tuple2 integer integer -> T
    = \(ds : Tuple2 integer integer) -> `$WMkT` ds
in
mkT (Tuple2 {integer} {integer} 2 1)