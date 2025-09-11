let
  ~`$fMkNilInteger` : (\arep -> list arep) integer = []
  !lessThanEqualsInteger : integer -> integer -> bool = lessThanEqualsInteger
  !mkCons : all a. a -> list a -> list a = mkCons
  !subtractInteger : integer -> integer -> integer = subtractInteger
  !caseList' : all a r. r -> (a -> list a -> r) -> list a -> r
    = /\a r -> \(z : r) (f : a -> list a -> r) (xs : list a) -> case r xs [f, z]
in
letrec
  ~take : all a. (\arep -> list arep) a -> integer -> list a -> list a
    = /\a ->
        \(`$dMkNil` : (\arep -> list arep) a) (n : integer) ->
          let
            !n : integer = n
          in
          \(l : list a) ->
            let
              !l : list a = l
            in
            case
              (all dead. list a)
              (lessThanEqualsInteger n 0)
              [ (/\dead ->
                   caseList'
                     {a}
                     {list a}
                     `$dMkNil`
                     (\(x : a) ->
                        let
                          !x : a = x
                        in
                        \(xs : list a) ->
                          let
                            !xs : list a = xs
                          in
                          mkCons
                            {a}
                            x
                            (take {a} `$dMkNil` (subtractInteger n 1) xs))
                     l)
              , (/\dead -> `$dMkNil`) ]
              {all dead. dead}
in
let
  data (Maybe :: * -> *) a | Maybe_match where
    Just : a -> Maybe a
    Nothing : Maybe a
  ~uniqueElement : all a. list a -> Maybe a
    = /\a ->
        caseList'
          {a}
          {Maybe a}
          (Nothing {a})
          (\(x : a) ->
             let
               !x : a = x
             in
             caseList'
               {a}
               {Maybe a}
               (Just {a} x)
               (\(ds : a) (ds : list a) -> Nothing {a}))
in
\(xs : list integer) ->
  let
    !xs : list integer = xs
  in
  uniqueElement {integer} (take {integer} `$fMkNilInteger` 1 xs)