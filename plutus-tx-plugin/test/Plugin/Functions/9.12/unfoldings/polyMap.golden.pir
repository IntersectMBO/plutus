let
  !addInteger : integer -> integer -> integer = addInteger
  ~addInteger : integer -> integer -> integer
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in addInteger x y
in
letrec
  data (List :: * -> *) a | List_match where
    Nil : List a
    Cons : a -> List a -> List a
in
let
  ~build : all a. (all b. (a -> b -> b) -> b -> b) -> List a
    = /\a ->
        \(g : all b. (a -> b -> b) -> b -> b) ->
          g {List a} (\(ds : a) (ds : List a) -> Cons {a} ds ds) (Nil {a})
in
letrec
  ~mapDirect : all a b. (a -> b) -> List a -> List b
    = /\a b ->
        \(f : a -> b) ->
          let
            !f : a -> b = f
          in
          \(l : List a) ->
            let
              !l : List a = l
            in
            List_match
              {a}
              l
              {all dead. List b}
              (/\dead -> Nil {b})
              (\(x : a) (xs : List a) ->
                 /\dead -> Cons {b} (f x) (mapDirect {a} {b} f xs))
              {all dead. dead}
in
mapDirect
  {integer}
  {integer}
  (addInteger 1)
  (build {integer} (/\a -> \(c : integer -> a -> a) (n : a) -> c 0 (c 1 n)))