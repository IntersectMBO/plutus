let
  !equalsInteger : integer -> integer -> bool = equalsInteger
  ~equalsInteger : integer -> integer -> bool
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in equalsInteger x y
  ~`$fEqInteger` : (\a -> a -> a -> bool) integer = equalsInteger
  !caseList' : all a r. r -> (a -> list a -> r) -> list a -> r
    = /\a r -> \(z : r) (f : a -> list a -> r) (xs : list a) -> case r xs [f, z]
  ~elem : all a. (\a -> a -> a -> bool) a -> a -> list a -> bool
    = /\a ->
        \(`$dEq` : (\a -> a -> a -> bool) a) (a : a) ->
          let
            !a : a = a
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
                         (`$dEq` a x)
                         [(/\dead -> go xs), (/\dead -> True)]
                         {all dead. dead})
          in
          go
  ~notElem : all a. (\a -> a -> a -> bool) a -> a -> list a -> bool
    = /\a ->
        \(`$dEq` : (\a -> a -> a -> bool) a) (a : a) ->
          let
            !a : a = a
            ~g : list a -> bool = elem {a} `$dEq` a
          in
          \(eta : list a) ->
            let
              !x : list a = eta
              !g : list a -> bool = g
            in
            case bool (g x) [True, False]
in
\(xs : list integer) ->
  let
    !xs : list integer = xs
  in
  notElem {integer} `$fEqInteger` 42 xs