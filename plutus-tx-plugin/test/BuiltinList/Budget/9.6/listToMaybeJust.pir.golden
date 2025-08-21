let
  data (Maybe :: * -> *) a | Maybe_match where
    Just : a -> Maybe a
    Nothing : Maybe a
  !caseList' : all a r. r -> (a -> list a -> r) -> list a -> r
    = /\a r -> \(z : r) (f : a -> list a -> r) (xs : list a) -> case r xs [f, z]
  ~listToMaybe : all a. list a -> Maybe a
    = /\a ->
        caseList'
          {a}
          {Maybe a}
          (Nothing {a})
          (\(x : a) -> let !x : a = x in \(ds : list a) -> Just {a} x)
in
\(xs : list integer) -> let !xs : list integer = xs in listToMaybe {integer} xs