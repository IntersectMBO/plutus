let
  data (Tuple2 :: * -> * -> *) a b | Tuple2_match where
    Tuple2 : a -> b -> Tuple2 a b
  !z : Tuple2 integer integer
    = trace
        {Tuple2 integer integer}
        "z"
        (trace {Tuple2 integer integer} "y" (Tuple2 {integer} {integer} 1 2))
in
Tuple2_match
  {integer}
  {integer}
  (trace {Tuple2 integer integer} "zz" z)
  {bool}
  (\(zz : integer) (ds : integer) ->
     let
       !t : integer = trace {integer} "t" zz
     in
     equalsInteger (trace {integer} "x" 0) t)