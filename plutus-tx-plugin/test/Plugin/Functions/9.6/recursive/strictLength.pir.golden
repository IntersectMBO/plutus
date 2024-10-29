letrec
  data (List :: * -> *) a | List_match where
    Nil : List a
    Cons : a -> List a -> List a
in
let
  !addInteger : integer -> integer -> integer = addInteger
  ~addInteger : integer -> integer -> integer
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in addInteger x y
  ~lengthStrict : all a. List a -> integer
    = /\a ->
        letrec
          ~go : integer -> List a -> integer
            = \(acc : integer) ->
                let
                  !acc : integer = acc
                in
                \(ds : List a) ->
                  List_match
                    {a}
                    ds
                    {all dead. integer}
                    (/\dead -> acc)
                    (\(ds : a) (tl : List a) ->
                       /\dead -> go (addInteger acc 1) tl)
                    {all dead. dead}
        in
        \(l : List a) -> let !l : List a = l in go 0 l
in
lengthStrict {integer}