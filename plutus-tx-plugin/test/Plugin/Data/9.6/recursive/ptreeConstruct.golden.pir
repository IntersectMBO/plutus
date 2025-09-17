let
  data (Tuple2 :: * -> * -> *) a b | Tuple2_match where
    Tuple2 : a -> b -> Tuple2 a b
in
letrec
  data (B :: * -> *) a | B_match where
    One : a -> B a
    Two : B (Tuple2 a a) -> B a
in
let
  ~`$WOne` : all a. a -> B a
    = /\a -> \(conrep : a) -> let !conrep : a = conrep in One {a} conrep
  ~`$WTwo` : all a. B (Tuple2 a a) -> B a
    = /\a ->
        \(conrep : B (Tuple2 a a)) ->
          let
            !conrep : B (Tuple2 a a) = conrep
          in
          Two {a} conrep
in
`$WTwo`
  {integer}
  (`$WTwo`
     {Tuple2 integer integer}
     (`$WOne`
        {Tuple2 (Tuple2 integer integer) (Tuple2 integer integer)}
        (Tuple2
           {Tuple2 integer integer}
           {Tuple2 integer integer}
           (Tuple2 {integer} {integer} 1 2)
           (Tuple2 {integer} {integer} 3 4))))