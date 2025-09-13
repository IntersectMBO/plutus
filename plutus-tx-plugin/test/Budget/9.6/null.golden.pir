letrec
  data (List :: * -> *) a | List_match where
    Nil : List a
    Cons : a -> List a -> List a
in
let
  !ds : List integer
    = (let
          a = List integer
        in
        \(c : integer -> a -> a) (n : a) ->
          c 1 (c 2 (c 3 (c 4 (c 5 (c 6 (c 7 (c 8 (c 9 (c 10 n))))))))))
        (\(ds : integer) (ds : List integer) -> Cons {integer} ds ds)
        (Nil {integer})
in
List_match
  {integer}
  ds
  {bool}
  True
  (\(ipv : integer) (ipv : List integer) -> False)