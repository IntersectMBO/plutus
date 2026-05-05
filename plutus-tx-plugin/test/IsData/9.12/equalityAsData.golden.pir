let
  !equalsData : data -> data -> bool = equalsData
  ~equalsData : data -> data -> bool
    = \(d : data) ->
        let
          !d : data = d
        in
        \(d : data) -> let !d : data = d in equalsData d d
  ~`$fEqSecretlyData` : (\a -> a -> a -> bool) data = equalsData
  ~`==` : all a. (\a -> a -> a -> bool) a -> a -> a -> bool
    = /\a -> \(v : (\a -> a -> a -> bool) a) -> v
in
\(x : data) ->
  let
    !nt : data = x
  in
  \(y : data) -> let !nt : data = y in `==` {data} `$fEqSecretlyData` nt nt