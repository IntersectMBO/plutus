let
  !equalsInteger : integer -> integer -> bool = equalsInteger
  ~equalsInteger : integer -> integer -> bool
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in equalsInteger x y
  ~`$fEqInteger` : (\a -> a -> a -> bool) integer = equalsInteger
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
  ~`++` : all a. list a -> list a -> list a
    = /\a ->
        \(l : list a) ->
          let
            !l : list a = l
          in
          \(r : list a) ->
            let
              !r : list a = r
            in
            foldr {a} {list a} (mkCons {a}) r l
  ~append : all a. list a -> list a -> list a = `++`
  ~elemBy : all a. (a -> a -> bool) -> a -> list a -> bool
    = /\a ->
        \(eq : a -> a -> bool) ->
          let
            !eq : a -> a -> bool = eq
          in
          \(y : a) ->
            let
              !y : a = y
            in
            letrec
              ~go : list a -> bool
                = caseList'
                    {a}
                    {bool}
                    False
                    (\(x : a) ->
                       let
                         !x : a = x
                       in
                       \(xs : list a) ->
                         let
                           !xs : list a = xs
                         in
                         case
                           (all dead. bool)
                           (eq x y)
                           [(/\dead -> go xs), (/\dead -> True)]
                           {all dead. dead})
            in
            go
  ~nubBy : all a. (\arep -> list arep) a -> (a -> a -> bool) -> list a -> list a
    = /\a ->
        \(`$dMkNil` : (\arep -> list arep) a) ->
          let
            !x : list a = `$dMkNil`
          in
          \(eq : a -> a -> bool) ->
            let
              !eq : a -> a -> bool = eq
            in
            letrec
              ~go : list a -> list a -> list a
                = \(l : list a) ->
                    let
                      !l : list a = l
                    in
                    \(xs : list a) ->
                      let
                        !xs : list a = xs
                      in
                      caseList'
                        {a}
                        {list a}
                        `$dMkNil`
                        (\(y : a) ->
                           let
                             !y : a = y
                           in
                           \(ys : list a) ->
                             let
                               !ys : list a = ys
                             in
                             case
                               (all dead. list a)
                               (elemBy {a} eq y xs)
                               [ (/\dead ->
                                    mkCons {a} y (go ys (mkCons {a} y xs)))
                               , (/\dead -> go ys xs) ]
                               {all dead. dead})
                        l
            in
            \(eta : list a) -> let !y : list a = eta in go y x
  ~nub :
     all a.
       (\a -> a -> a -> bool) a -> (\arep -> list arep) a -> list a -> list a
    = /\a ->
        \(`$dEq` : (\a -> a -> a -> bool) a)
         (`$dMkNil` : (\arep -> list arep) a) ->
          nubBy {a} `$dMkNil` `$dEq`
in
\(xs : list integer) ->
  let
    !xs : list integer = xs
  in
  nub {integer} `$fEqInteger` `$fMkNilInteger` (append {integer} xs xs)