let
  ~`$fMkNilInteger` : (\arep -> list arep) integer = []
  data (Maybe :: * -> *) a | Maybe_match where
    Just : a -> Maybe a
    Nothing : Maybe a
  !caseList' : all a r. r -> (a -> list a -> r) -> list a -> r
    = /\a r -> \(z : r) (f : a -> list a -> r) (xs : list a) -> case r xs [f, z]
  !mkCons : all a. a -> list a -> list a = mkCons
  ~mapMaybe :
     all a b. (\arep -> list arep) b -> (a -> Maybe b) -> list a -> list b
    = /\a b ->
        \(`$dMkNil` : (\arep -> list arep) b) (f : a -> Maybe b) ->
          let
            !f : a -> Maybe b = f
          in
          letrec
            ~go : list a -> list b
              = caseList'
                  {a}
                  {list b}
                  `$dMkNil`
                  (\(x : a) ->
                     let
                       !x : a = x
                     in
                     \(xs : list a) ->
                       let
                         !xs : list a = xs
                       in
                       Maybe_match
                         {b}
                         (f x)
                         {all dead. list b}
                         (\(y : b) -> /\dead -> mkCons {b} y (go xs))
                         (/\dead -> go xs)
                         {all dead. dead})
          in
          go
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
  mapMaybe
    {integer}
    {integer}
    `$fMkNilInteger`
    (\(x : integer) ->
       let
         !x : integer = x
       in
       case
         (all dead. Maybe integer)
         (odd x)
         [(/\dead -> Nothing {integer}), (/\dead -> Just {integer} x)]
         {all dead. dead})
    xs