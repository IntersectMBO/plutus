let
  ~`$fMkNilInteger` : (\arep -> list arep) integer = []
  !lessThanEqualsInteger : integer -> integer -> bool = lessThanEqualsInteger
  !mkCons : all a. a -> list a -> list a = mkCons
  !subtractInteger : integer -> integer -> integer = subtractInteger
  ~replicate : all a. (\arep -> list arep) a -> integer -> a -> list a
    = /\a ->
        \(`$dMkNil` : (\arep -> list arep) a) (n : integer) ->
          let
            !n : integer = n
          in
          \(x : a) ->
            let
              !x : a = x
            in
            letrec
              ~go : integer -> list a
                = \(n : integer) ->
                    let
                      !n : integer = n
                    in
                    case
                      (all dead. list a)
                      (lessThanEqualsInteger n 0)
                      [ (/\dead -> mkCons {a} x (go (subtractInteger n 1)))
                      , (/\dead -> `$dMkNil`) ]
                      {all dead. dead}
            in
            go n
in
\(ds : list integer) -> replicate {integer} `$fMkNilInteger` 10 0