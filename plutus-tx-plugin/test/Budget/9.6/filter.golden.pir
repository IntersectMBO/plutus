letrec
  data (List :: * -> *) a | List_match where
    Nil : List a
    Cons : a -> List a -> List a
in
letrec
  !go : List integer -> List integer
    = \(ds : List integer) ->
        List_match
          {integer}
          ds
          {all dead. List integer}
          (/\dead -> Nil {integer})
          (\(x : integer) (xs : List integer) ->
             /\dead ->
               let
                 !xs : List integer = go xs
               in
               case
                 (all dead. List integer)
                 (equalsInteger 0 (modInteger x 2))
                 [(/\dead -> xs), (/\dead -> Cons {integer} x xs)]
                 {all dead. dead})
          {all dead. dead}
in
let
  !ls : List integer
    = (let
          a = List integer
        in
        \(c : integer -> a -> a) (n : a) ->
          c 1 (c 2 (c 3 (c 4 (c 5 (c 6 (c 7 (c 8 (c 9 (c 10 n))))))))))
        (\(ds : integer) (ds : List integer) -> Cons {integer} ds ds)
        (Nil {integer})
in
go ls