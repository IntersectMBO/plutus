let
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
in
\(xs : list integer) -> let !xs : list integer = xs in `++` {integer} xs xs