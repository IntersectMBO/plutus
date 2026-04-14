let
  !cons :
     all a.
       (\a -> a -> data) a -> a -> (\a -> list data) a -> (\a -> list data) a
    = /\a ->
        \(`$dToData` : (\a -> a -> data) a)
         (h : a)
         (eta : (\a -> list data) a) ->
          mkCons {data} (`$dToData` h) eta
in
\(x : integer) (y : integer) (z : integer) ->
  (let
      b = (\a -> list data) integer
    in
    /\c a -> \(f : b -> c) (g : a -> b) (x : a) -> f (g x))
    {(\a -> list data) integer}
    {(\a -> list data) integer}
    (cons {integer} (\(i : integer) -> iData i) x)
    ((let
         b = (\a -> list data) integer
       in
       /\c a -> \(f : b -> c) (g : a -> b) (x : a) -> f (g x))
       {(\a -> list data) integer}
       {(\a -> list data) integer}
       (cons {integer} (\(i : integer) -> iData i) y)
       (cons {integer} (\(i : integer) -> iData i) z))
    []