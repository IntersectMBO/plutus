let
  !addInteger : integer -> integer -> integer = addInteger
  !caseList' : all a r. r -> (a -> list a -> r) -> list a -> r
    = /\a r -> \(z : r) (f : a -> list a -> r) (xs : list a) -> case r xs [f, z]
  !mkCons : all a. a -> list a -> list a = mkCons
  ~findIndices : all a. (a -> bool) -> list a -> list integer
    = /\a ->
        \(p : a -> bool) ->
          let
            !p : a -> bool = p
          in
          letrec
            ~go : integer -> list a -> list integer
              = \(i : integer) ->
                  let
                    !i : integer = i
                  in
                  caseList'
                    {a}
                    {list integer}
                    []
                    (\(x : a) ->
                       let
                         !x : a = x
                       in
                       \(xs : list a) ->
                         let
                           !xs : list a = xs
                           !indices : list integer = go (addInteger i 1) xs
                         in
                         case
                           (all dead. list integer)
                           (p x)
                           [ (/\dead -> indices)
                           , (/\dead -> mkCons {integer} i indices) ]
                           {all dead. dead})
          in
          go 0
  !equalsInteger : integer -> integer -> bool = equalsInteger
  !modInteger : integer -> integer -> integer = modInteger
  ~odd : integer -> bool
    = \(n : integer) ->
        let
          !n : integer = n
          !x : integer = modInteger n 2
        in
        case bool (equalsInteger x 0) [True, False]
in
\(xs : list integer) ->
  let
    !xs : list integer = xs
  in
  findIndices {integer} odd xs