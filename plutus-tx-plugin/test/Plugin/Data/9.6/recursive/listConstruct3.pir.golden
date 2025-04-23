letrec
  data (List :: * -> *) a | List_match where
    Nil : List a
    Cons : a -> List a -> List a
in
Cons {integer} 1 (Cons {integer} 2 (Cons {integer} 3 (Nil {integer})))