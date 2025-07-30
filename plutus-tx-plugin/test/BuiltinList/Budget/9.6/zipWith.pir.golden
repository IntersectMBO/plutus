let
  !addInteger : integer -> integer -> integer = addInteger
  ~addInteger : integer -> integer -> integer
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in addInteger x y
  ~`$fAdditiveSemigroupInteger` : (\a -> a -> a -> a) integer = addInteger
  ~`$fMkNilInteger` : (\arep -> list arep) integer = []
  ~`+` : all a. (\a -> a -> a -> a) a -> a -> a -> a
    = /\a -> \(v : (\a -> a -> a -> a) a) -> v
  !caseList' : all a r. r -> (a -> list a -> r) -> list a -> r
    = /\a r -> \(z : r) (f : a -> list a -> r) (xs : list a) -> case r xs [f, z]
  !mkCons : all a. a -> list a -> list a = mkCons
  ~zipWith :
     all a b c.
       (\arep -> list arep) c -> (a -> b -> c) -> list a -> list b -> list c
    = /\a b c ->
        \(`$dMkNil` : (\arep -> list arep) c) (f : a -> b -> c) ->
          let
            !f : a -> b -> c = f
          in
          letrec
            ~go : list a -> list b -> list c
              = \(xs : list a) ->
                  let
                    !xs : list a = xs
                  in
                  \(ys : list b) ->
                    let
                      !ys : list b = ys
                    in
                    caseList'
                      {a}
                      {list c}
                      `$dMkNil`
                      (\(x : a) ->
                         let
                           !x : a = x
                         in
                         \(xs' : list a) ->
                           let
                             !xs' : list a = xs'
                           in
                           caseList'
                             {b}
                             {list c}
                             `$dMkNil`
                             (\(y : b) ->
                                let
                                  !y : b = y
                                in
                                \(ys' : list b) ->
                                  let
                                    !ys' : list b = ys'
                                  in
                                  mkCons {c} (f x y) (go xs' ys'))
                             ys)
                      xs
          in
          \(eta : list a) (eta : list b) -> go eta eta
in
\(xs : list integer) ->
  let
    !xs : list integer = xs
  in
  zipWith
    {integer}
    {integer}
    {integer}
    `$fMkNilInteger`
    (`+` {integer} `$fAdditiveSemigroupInteger`)
    xs
    xs