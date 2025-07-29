let
  data (Tuple2 :: * -> * -> *) a b | Tuple2_match where
    Tuple2 : a -> b -> Tuple2 a b
  data (Maybe :: * -> *) a | Maybe_match where
    Just : a -> Maybe a
    Nothing : Maybe a
  !caseList' : all a r. r -> (a -> list a -> r) -> list a -> r
    = /\a r -> \(z : r) (f : a -> list a -> r) (xs : list a) -> case r xs [f, z]
  ~uncons : all a. list a -> Maybe (Tuple2 a (list a))
    = /\a ->
        caseList'
          {a}
          {Maybe (Tuple2 a (list a))}
          (Nothing {Tuple2 a (list a)})
          (\(h : a) ->
             let
               !h : a = h
             in
             \(t : list a) ->
               let
                 !t : list a = t
               in
               Just {Tuple2 a (list a)} (Tuple2 {a} {list a} h t))
in
\(xs : list integer) -> let !xs : list integer = xs in uncons {integer} xs