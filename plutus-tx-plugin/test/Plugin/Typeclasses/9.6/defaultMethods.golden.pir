let
  data (DefaultMethods :: * -> *) a | DefaultMethods_match where
    CConsDefaultMethods : (a -> integer) -> (a -> integer) -> DefaultMethods a
  ~method : all a. DefaultMethods a -> a -> integer
    = /\a ->
        \(v : DefaultMethods a) ->
          DefaultMethods_match
            {a}
            v
            {a -> integer}
            (\(v : a -> integer) (v : a -> integer) -> v)
  ~f : all a. DefaultMethods a -> a -> integer
    = /\a ->
        \(`$dDefaultMethods` : DefaultMethods a) (a : a) ->
          let
            !a : a = a
          in
          method {a} `$dDefaultMethods` a
  ~`$fDefaultMethodsInteger_$cmethod` : integer -> integer = \(a : integer) -> a
  !addInteger : integer -> integer -> integer = addInteger
  ~`$fDefaultMethodsInteger_$cmethod` : integer -> integer
    = \(a : integer) -> let !a : integer = a in addInteger a 1
  ~`$fDefaultMethodsInteger` : DefaultMethods integer
    = CConsDefaultMethods
        {integer}
        `$fDefaultMethodsInteger_$cmethod`
        `$fDefaultMethodsInteger_$cmethod`
in
\(ds : integer) ->
  let
    !ds : integer = ds
  in
  f {integer} `$fDefaultMethodsInteger` ds