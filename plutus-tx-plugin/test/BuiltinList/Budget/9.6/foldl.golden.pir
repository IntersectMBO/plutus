let
  !multiplyInteger : integer -> integer -> integer = multiplyInteger
  ~multiplyInteger : integer -> integer -> integer
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in multiplyInteger x y
  ~`$fMultiplicativeSemigroupInteger` : (\a -> a -> a -> a) integer
    = multiplyInteger
  ~`*` : all a. (\a -> a -> a -> a) a -> a -> a -> a
    = /\a -> \(v : (\a -> a -> a -> a) a) -> v
  !caseList' : all a r. r -> (a -> list a -> r) -> list a -> r
    = /\a r -> \(z : r) (f : a -> list a -> r) (xs : list a) -> case r xs [f, z]
  ~foldl : all a b. (b -> a -> b) -> b -> list a -> b
    = /\a b ->
        \(f : b -> a -> b) ->
          let
            !f : b -> a -> b = f
          in
          letrec
            ~go : b -> list a -> b
              = \(acc : b) ->
                  let
                    !acc : b = acc
                  in
                  caseList'
                    {a}
                    {b}
                    acc
                    (\(x : a) ->
                       let
                         !x : a = x
                       in
                       \(xs : list a) ->
                         let
                           !xs : list a = xs
                         in
                         go (f acc x) xs)
          in
          \(eta : b) -> go eta
in
\(xs : list integer) ->
  let
    !xs : list integer = xs
  in
  foldl
    {integer}
    {integer}
    (`*` {integer} `$fMultiplicativeSemigroupInteger`)
    1
    xs