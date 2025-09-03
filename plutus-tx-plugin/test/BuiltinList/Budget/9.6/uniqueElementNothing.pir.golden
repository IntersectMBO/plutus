let
  ~`$fMkNilInteger` : (\arep -> list arep) integer = []
  ~mkNil : all arep. (\arep -> list arep) arep -> list arep
    = /\arep -> \(v : (\arep -> list arep) arep) -> v
  ~empty : all a. (\arep -> list arep) a -> list a = mkNil
  data (Maybe :: * -> *) a | Maybe_match where
    Just : a -> Maybe a
    Nothing : Maybe a
  !caseList' : all a r. r -> (a -> list a -> r) -> list a -> r
    = /\a r -> \(z : r) (f : a -> list a -> r) (xs : list a) -> case r xs [f, z]
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
\(ds : list integer) ->
  uniqueElement {integer} (empty {integer} `$fMkNilInteger`)