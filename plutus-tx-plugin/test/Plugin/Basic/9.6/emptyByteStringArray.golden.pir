let
  ~`$fMkNilBuiltinByteString` : (\arep -> list arep) bytestring = []
  ~mkNil : all arep. (\arep -> list arep) arep -> list arep
    = /\arep -> \(v : (\arep -> list arep) arep) -> v
in
mkNil {bytestring} `$fMkNilBuiltinByteString`