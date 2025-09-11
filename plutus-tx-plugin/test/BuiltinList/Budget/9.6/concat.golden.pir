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
  ~concat : all a. (\arep -> list arep) a -> list (list a) -> list a
    = /\a ->
        \(`$dMkNil` : (\arep -> list arep) a) ->
          let
            !acc : list a = `$dMkNil`
          in
          letrec
            ~go : list (list a) -> list a
              = caseList'
                  {list a}
                  {list a}
                  acc
                  (\(x : list a) ->
                     let
                       !x : list a = x
                     in
                     \(xs : list (list a)) ->
                       let
                         !xs : list (list a) = xs
                         !r : list a = go xs
                       in
                       foldr {a} {list a} (mkCons {a}) r x)
          in
          go
in
\(xss : list (list integer)) ->
  let
    !xss : list (list integer) = xss
  in
  concat {integer} `$fMkNilInteger` xss