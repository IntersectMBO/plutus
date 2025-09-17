let
  !addInteger : integer -> integer -> integer = addInteger
  ~addInteger : integer -> integer -> integer
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in addInteger x y
  ~`$fAdditiveSemigroupInteger` : (\a -> a -> a -> a) integer = addInteger
  ~`+` : all a. (\a -> a -> a -> a) a -> a -> a -> a
    = /\a -> \(v : (\a -> a -> a -> a) a) -> v
  !caseList' : all a r. r -> (a -> list a -> r) -> list a -> r
    = /\a r -> \(z : r) (f : a -> list a -> r) (xs : list a) -> case r xs [f, z]
  ~foldr : all a b. (a -> b -> b) -> b -> list a -> b
    = /\a b ->
        \(f : a -> b -> b) ->
          let
            !f : a -> b -> b = f
          in
          \(acc : b) ->
            let
              !acc : b = acc
            in
            letrec
              ~go : list a -> b
                = caseList'
                    {a}
                    {b}
                    acc
                    (\(x : a) ->
                       let
                         !x : a = x
                       in
                       \(xs : list a) -> let !xs : list a = xs in f x (go xs))
            in
            go
in
\(xs : list integer) ->
  let
    !xs : list integer = xs
  in
  foldr {integer} {integer} (`+` {integer} `$fAdditiveSemigroupInteger`) 0 xs