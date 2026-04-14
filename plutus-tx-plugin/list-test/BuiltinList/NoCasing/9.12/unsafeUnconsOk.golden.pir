let
  data (Tuple :: * -> * -> *) a b | Tuple_match where
    Tuple2 : a -> b -> Tuple a b
  !unsafeCaseList : all a r. (a -> list a -> r) -> list a -> r
    = /\a r ->
        \(f : a -> list a -> r) (xs : list a) ->
          f (headList {a} xs) (tailList {a} xs)
  ~unsafeUncons : all a. list a -> Tuple a (list a)
    = /\a ->
        unsafeCaseList
          {a}
          {Tuple a (list a)}
          (\(ds : a) (ds : list a) -> Tuple2 {a} {list a} ds ds)
in
\(xs : list integer) -> let !xs : list integer = xs in unsafeUncons {integer} xs