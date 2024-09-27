let
  data (Tuple2 :: * -> * -> *) a b | Tuple2_match where
    Tuple2 : a -> b -> Tuple2 a b
  !addInteger : integer -> integer -> integer = addInteger
  ~`$csize` :
     all a b.
       (\a -> a -> integer) a -> (\a -> a -> integer) b -> Tuple2 a b -> integer
    = /\a b ->
        \(`$dSized` : (\a -> a -> integer) a)
         (`$dSized` : (\a -> a -> integer) b)
         (ds : Tuple2 a b) ->
          Tuple2_match
            {a}
            {b}
            ds
            {integer}
            (\(a : a) (b : b) ->
               let
                 !x : integer = `$dSized` a
                 !y : integer = `$dSized` b
               in
               addInteger x y)
  ~`$fSizedTuple2` :
     all a b.
       (\a -> a -> integer) a ->
       (\a -> a -> integer) b ->
       (\a -> a -> integer) (Tuple2 a b)
    = `$csize`
  ~`$csize` : integer -> integer = \(x : integer) -> x
  ~`$fSizedInteger` : (\a -> a -> integer) integer = `$csize`
  ~`$dSized` : (\a -> a -> integer) (Tuple2 integer integer)
    = `$fSizedTuple2` {integer} {integer} `$fSizedInteger` `$fSizedInteger`
  ~size : all a. (\a -> a -> integer) a -> a -> integer
    = /\a -> \(v : (\a -> a -> integer) a) -> v
in
\(ds : integer) ->
  let
    !ds : integer = ds
  in
  \(ds : integer) ->
    let
      !ds : integer = ds
    in
    size {Tuple2 integer integer} `$dSized` (Tuple2 {integer} {integer} ds ds)