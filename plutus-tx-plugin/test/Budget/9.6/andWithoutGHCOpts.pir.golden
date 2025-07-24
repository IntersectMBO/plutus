(let
    data Ordering | Ordering_match where
      EQ : Ordering
      GT : Ordering
      LT : Ordering
    data (Ord :: * -> *) a | Ord_match where
      CConsOrd :
        (\a -> a -> a -> bool) a ->
        (a -> a -> Ordering) ->
        (a -> a -> bool) ->
        (a -> a -> bool) ->
        (a -> a -> bool) ->
        (a -> a -> bool) ->
        (a -> a -> a) ->
        (a -> a -> a) ->
        Ord a
    !ifThenElse : all a. bool -> a -> a -> a
      = /\a -> \(b : bool) (x : a) (y : a) -> case a b [y, x]
    !`$fOrdInteger` : Ord integer
      = CConsOrd
          {integer}
          (\(x : integer) (y : integer) -> equalsInteger x y)
          (\(eta : integer) (eta : integer) ->
             case
               (all dead. Ordering)
               (equalsInteger eta eta)
               [ (/\dead ->
                    case
                      (all dead. Ordering)
                      (lessThanEqualsInteger eta eta)
                      [(/\dead -> GT), (/\dead -> LT)]
                      {all dead. dead})
               , (/\dead -> EQ) ]
               {all dead. dead})
          (\(x : integer) (y : integer) -> lessThanInteger x y)
          (\(x : integer) (y : integer) -> lessThanEqualsInteger x y)
          (\(x : integer) (y : integer) ->
             ifThenElse {bool} (lessThanEqualsInteger x y) False True)
          (\(x : integer) (y : integer) ->
             ifThenElse {bool} (lessThanInteger x y) False True)
          (\(x : integer) (y : integer) ->
             case
               (all dead. integer)
               (lessThanEqualsInteger x y)
               [(/\dead -> x), (/\dead -> y)]
               {all dead. dead})
          (\(x : integer) (y : integer) ->
             case
               (all dead. integer)
               (lessThanEqualsInteger x y)
               [(/\dead -> y), (/\dead -> x)]
               {all dead. dead})
    !`<` : all a. Ord a -> a -> a -> bool
      = /\a ->
          \(v : Ord a) ->
            Ord_match
              {a}
              v
              {a -> a -> bool}
              (\(v : (\a -> a -> a -> bool) a)
                (v : a -> a -> Ordering)
                (v : a -> a -> bool)
                (v : a -> a -> bool)
                (v : a -> a -> bool)
                (v : a -> a -> bool)
                (v : a -> a -> a)
                (v : a -> a -> a) ->
                 v)
  in
  \(x : integer) (y : integer) ->
    case
      (all dead. bool)
      (`<` {integer} `$fOrdInteger` x 3)
      [(/\dead -> False), (/\dead -> `<` {integer} `$fOrdInteger` y 3)]
      {all dead. dead})
  4
  4