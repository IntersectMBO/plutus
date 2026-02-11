let
  data (Tuple :: * -> * -> *) a b | Tuple_match where
    Tuple2 : a -> b -> Tuple a b
  !z : Tuple integer integer
    = trace
        {Tuple integer integer}
        "z"
        (trace {Tuple integer integer} "y" (Tuple2 {integer} {integer} 1 2))
in
Tuple_match
  {integer}
  {integer}
  (trace {Tuple integer integer} "zz" z)
  {bool}
  (\(zz : integer) (ds : integer) ->
     let
       !t : integer = trace {integer} "t" zz
     in
     equalsInteger (trace {integer} "x" 0) t)