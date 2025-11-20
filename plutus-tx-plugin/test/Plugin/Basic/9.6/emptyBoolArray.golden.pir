let
  ~`$fMkNilBool` : (\arep -> list arep) bool = []
  ~mkNil : all arep. (\arep -> list arep) arep -> list arep
    = /\arep -> \(v : (\arep -> list arep) arep) -> v
in
mkNil {bool} `$fMkNilBool`