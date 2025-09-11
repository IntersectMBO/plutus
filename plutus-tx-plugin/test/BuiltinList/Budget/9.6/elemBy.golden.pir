let
  !caseList' : all a r. r -> (a -> list a -> r) -> list a -> r
    = /\a r -> \(z : r) (f : a -> list a -> r) (xs : list a) -> case r xs [f, z]
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
  !lessThanEqualsInteger : integer -> integer -> bool = lessThanEqualsInteger
  ~lessThanEqualsInteger : integer -> integer -> bool
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in lessThanEqualsInteger x y
in
\(xs : list integer) ->
  let
    !xs : list integer = xs
  in
  elemBy {integer} lessThanEqualsInteger 0 xs