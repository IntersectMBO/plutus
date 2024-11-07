let
  data (MyPolyData :: * -> * -> *) a b | MyPolyData_match where
    Poly : a -> b -> MyPolyData a b
    Poly : a -> MyPolyData a b
  ~`$WPoly` : all a b. a -> b -> MyPolyData a b
    = /\a b ->
        \(conrep : a) ->
          let
            !conrep : a = conrep
          in
          \(conrep : b) ->
            let
              !conrep : b = conrep
            in
            Poly {a} {b} conrep conrep
in
`$WPoly` {integer} {integer} 1 2