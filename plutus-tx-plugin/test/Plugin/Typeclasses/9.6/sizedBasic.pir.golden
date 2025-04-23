let
  ~`$csize` : integer -> integer = \(x : integer) -> x
  ~`$fSizedInteger` : (\a -> a -> integer) integer = `$csize`
  ~size : all a. (\a -> a -> integer) a -> a -> integer
    = /\a -> \(v : (\a -> a -> integer) a) -> v
in
\(ds : integer) -> let !ds : integer = ds in size {integer} `$fSizedInteger` ds