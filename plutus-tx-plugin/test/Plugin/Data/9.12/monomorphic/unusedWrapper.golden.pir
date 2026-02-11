let
  data (Tuple :: * -> * -> *) a b | Tuple_match where
    Tuple2 : a -> b -> Tuple a b
  data T | T_match where
    MkT : Tuple integer integer -> T
  ~`$WMkT` : Tuple integer integer -> T
    = \(conrep : Tuple integer integer) ->
        let
          !conrep : Tuple integer integer = conrep
        in
        MkT conrep
  ~mkT : Tuple integer integer -> T
    = \(ds : Tuple integer integer) -> `$WMkT` ds
in
mkT (Tuple2 {integer} {integer} 2 1)