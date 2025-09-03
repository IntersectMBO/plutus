let
  !caseList' : all a r. r -> (a -> list a -> r) -> list a -> r
    = /\a r -> \(z : r) (f : a -> list a -> r) (xs : list a) -> case r xs [f, z]
  ~any : all a. (a -> bool) -> list a -> bool
    = /\a ->
        \(p : a -> bool) ->
          let
            !p : a -> bool = p
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
                         (p x)
                         [(/\dead -> go xs), (/\dead -> True)]
                         {all dead. dead})
          in
          go
  !ifThenElse : all a. bool -> a -> a -> a
    = /\a -> \(b : bool) (x : a) (y : a) -> case a b [y, x]
  ~or : list bool -> bool
    = any
        {bool}
        (\(x : bool) -> let !x : bool = x in ifThenElse {bool} x True False)
in
\(xs : list bool) -> let !xs : list bool = xs in or xs