let
  data (Tuple2 :: * -> * -> *) a b | Tuple2_match where
    Tuple2 : a -> b -> Tuple2 a b
  !unsafeCaseList : all a r. (a -> list a -> r) -> list a -> r
    = /\a r ->
        \(f : a -> list a -> r) (xs : list a) ->
          chooseList
            {a}
            {all dead. r}
            xs
            (/\dead -> error {r})
            (/\dead -> f (headList {a} xs) (tailList {a} xs))
            {r}
  ~unsafeUncons : all a. list a -> Tuple2 a (list a)
    = /\a ->
        unsafeCaseList
          {a}
          {Tuple2 a (list a)}
          (\(ds : a) (ds : list a) -> Tuple2 {a} {list a} ds ds)
in
\(xs : list integer) -> let !xs : list integer = xs in unsafeUncons {integer} xs