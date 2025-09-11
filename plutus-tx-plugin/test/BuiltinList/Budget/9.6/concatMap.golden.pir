let
  ~`$fMkNilInteger` : (\arep -> list arep) integer = []
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
  !mkCons : all a. a -> list a -> list a = mkCons
  ~concatMap :
     all a b. (\arep -> list arep) b -> (a -> list b) -> list a -> list b
    = /\a b ->
        \(`$dMkNil` : (\arep -> list arep) b) ->
          let
            !acc : list b = `$dMkNil`
          in
          \(f : a -> list b) ->
            let
              !f : a -> list b = f
            in
            letrec
              ~go : list a -> list b
                = caseList'
                    {a}
                    {list b}
                    acc
                    (\(x : a) ->
                       let
                         !x : a = x
                       in
                       \(xs : list a) ->
                         let
                           !xs : list a = xs
                           !ys : list b = go xs
                           !l : list b = f x
                         in
                         foldr {b} {list b} (mkCons {b}) ys l)
            in
            go
  !lessThanEqualsInteger : integer -> integer -> bool = lessThanEqualsInteger
  !subtractInteger : integer -> integer -> integer = subtractInteger
  ~replicate : all a. (\arep -> list arep) a -> integer -> a -> list a
    = /\a ->
        \(`$dMkNil` : (\arep -> list arep) a) (n : integer) ->
          let
            !n : integer = n
          in
          \(x : a) ->
            let
              !x : a = x
            in
            letrec
              ~go : integer -> list a
                = \(n : integer) ->
                    let
                      !n : integer = n
                    in
                    case
                      (all dead. list a)
                      (lessThanEqualsInteger n 0)
                      [ (/\dead -> mkCons {a} x (go (subtractInteger n 1)))
                      , (/\dead -> `$dMkNil`) ]
                      {all dead. dead}
            in
            go n
in
\(xss : list integer) ->
  let
    !xss : list integer = xss
  in
  concatMap
    {integer}
    {integer}
    `$fMkNilInteger`
    (replicate {integer} `$fMkNilInteger` 2)
    xss