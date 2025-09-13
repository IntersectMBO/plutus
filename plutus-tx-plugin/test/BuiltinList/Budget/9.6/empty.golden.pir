let
  ~`$fMkNilInteger` : (\arep -> list arep) integer = []
  ~mkNil : all arep. (\arep -> list arep) arep -> list arep
    = /\arep -> \(v : (\arep -> list arep) arep) -> v
  ~empty : all a. (\arep -> list arep) a -> list a = mkNil
in
\(ds : list integer) -> empty {integer} `$fMkNilInteger`