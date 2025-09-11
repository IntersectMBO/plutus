let
  ~`$fMkNilInteger` : (\arep -> list arep) integer = []
  !mkCons : all a. a -> list a -> list a = mkCons
  ~singleton : all a. (\arep -> list arep) a -> a -> list a
    = /\a ->
        \(`$dMkNil` : (\arep -> list arep) a) (x : a) ->
          let
            !x : a = x
          in
          mkCons {a} x `$dMkNil`
in
\(ds : list integer) -> singleton {integer} `$fMkNilInteger` 42