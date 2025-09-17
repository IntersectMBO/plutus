let
  ~`$fMkNilInteger` : (\arep -> list arep) integer = []
  !equalsInteger : integer -> integer -> bool = equalsInteger
  !modInteger : integer -> integer -> integer = modInteger
  ~even : integer -> bool
    = \(n : integer) ->
        let
          !n : integer = n
          !x : integer = modInteger n 2
        in
        equalsInteger x 0
  !caseList' : all a r. r -> (a -> list a -> r) -> list a -> r
    = /\a r -> \(z : r) (f : a -> list a -> r) (xs : list a) -> case r xs [f, z]
  !mkCons : all a. a -> list a -> list a = mkCons
  ~filter : all a. (\arep -> list arep) a -> (a -> bool) -> list a -> list a
    = /\a ->
        \(`$dMkNil` : (\arep -> list arep) a) ->
          let
            !acc : list a = `$dMkNil`
          in
          \(p : a -> bool) ->
            let
              !p : a -> bool = p
            in
            letrec
              ~go : list a -> list a
                = caseList'
                    {a}
                    {list a}
                    acc
                    (\(x : a) ->
                       let
                         !x : a = x
                       in
                       \(xs : list a) ->
                         let
                           !xs : list a = xs
                           !xs : list a = go xs
                         in
                         case
                           (all dead. list a)
                           (p x)
                           [(/\dead -> xs), (/\dead -> mkCons {a} x xs)]
                           {all dead. dead})
            in
            go
in
\(xs : list integer) ->
  let
    !xs : list integer = xs
  in
  filter {integer} `$fMkNilInteger` even xs