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
  ~concat : all a. List (List a) -> List a
    = /\a ->
        letrec
          ~go : List (List a) -> List a
            = \(ds : List (List a)) ->
                List_match
                  {List a}
                  ds
                  {all dead. List a}
                  (/\dead -> Nil {a})
                  (\(x : List a) ->
                     let
                       !l : List a = x
                     in
                     \(xs : List (List a)) ->
                       /\dead ->
                         let
                           !r : List a = go xs
                         in
                         letrec
                           ~go : List a -> List a
                             = \(ds : List a) ->
                                 List_match
                                   {a}
                                   ds
                                   {all dead. List a}
                                   (/\dead -> r)
                                   (\(x : a) (xs : List a) ->
                                      /\dead -> Cons {a} x (go xs))
                                   {all dead. dead}
                         in
                         go l)
                  {all dead. dead}
        in
        \(eta : List (List a)) -> go eta
in
concat
  {integer}
  (build
     {List integer}
     (/\a ->
        \(c : List integer -> a -> a) (n : a) ->
          c
            (build
               {integer}
               (/\a -> \(c : integer -> a -> a) (n : a) -> c 1 (c 2 n)))
            (c
               (build
                  {integer}
                  (/\a -> \(c : integer -> a -> a) (n : a) -> c 3 (c 4 n)))
               n)))