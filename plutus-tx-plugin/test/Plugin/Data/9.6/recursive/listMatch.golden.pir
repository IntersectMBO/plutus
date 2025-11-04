letrec
  data (List :: * -> *) a | List_match where
    Nil : List a
    Cons : a -> List a -> List a
in
\(ds : List integer) ->
  let
    !ds : List integer = ds
  in
  List_match {integer} ds {integer} 0 (\(x : integer) (ds : List integer) -> x)