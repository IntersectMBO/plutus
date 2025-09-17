let
  ~v : integer = 1
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
  ~v : integer -> integer -> integer
    = `+` {integer} `$fAdditiveSemigroupInteger`
  ~`$fMkNilInteger` : (\arep -> list arep) integer = []
  !caseList' : all a r. r -> (a -> list a -> r) -> list a -> r
    = /\a r -> \(z : r) (f : a -> list a -> r) (xs : list a) -> case r xs [f, z]
  !mkCons : all a. a -> list a -> list a = mkCons
  ~map : all a b. (\arep -> list arep) b -> (a -> b) -> list a -> list b
    = /\a b ->
        \(`$dMkNil` : (\arep -> list arep) b) (f : a -> b) ->
          let
            !f : a -> b = f
          in
          letrec
            ~go : list a -> list b
              = caseList'
                  {a}
                  {list b}
                  `$dMkNil`
                  (\(x : a) ->
                     let
                       !x : a = x
                     in
                     \(xs : list a) ->
                       let
                         !xs : list a = xs
                       in
                       mkCons {b} (f x) (go xs))
          in
          go
in
map {integer} {integer} `$fMkNilInteger` (\(v : integer) -> v v v)