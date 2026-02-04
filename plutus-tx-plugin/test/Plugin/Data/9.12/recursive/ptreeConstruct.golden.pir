let
  data (Tuple :: * -> * -> *) a b | Tuple_match where
    Tuple2 : a -> b -> Tuple a b
in
letrec
  data (B :: * -> *) a | B_match where
    One : a -> B a
    Two : B (Tuple a a) -> B a
in
let
  ~`$WOne` : all a. a -> B a
    = /\a -> \(conrep : a) -> let !conrep : a = conrep in One {a} conrep
  ~`$WTwo` : all a. B (Tuple a a) -> B a
    = /\a ->
        \(conrep : B (Tuple a a)) ->
          let
            !conrep : B (Tuple a a) = conrep
          in
          Two {a} conrep
in
`$WTwo`
  {integer}
  (`$WTwo`
     {Tuple integer integer}
     (`$WOne`
        {Tuple (Tuple integer integer) (Tuple integer integer)}
        (Tuple2
           {Tuple integer integer}
           {Tuple integer integer}
           (Tuple2 {integer} {integer} 1 2)
           (Tuple2 {integer} {integer} 3 4))))