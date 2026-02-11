let
  !equalsInteger : integer -> integer -> bool = equalsInteger
  !lessThanEqualsInteger : integer -> integer -> bool = lessThanEqualsInteger
  data Ordering | Ordering_match where
    EQ : Ordering
    GT : Ordering
    LT : Ordering
  ~`$fOrdInteger_$ccompare` : integer -> integer -> Ordering
    = \(eta : integer) ->
        let
          !x : integer = eta
        in
        \(eta : integer) ->
          let
            !y : integer = eta
          in
          case
            (all dead. Ordering)
            (equalsInteger x y)
            [ (/\dead ->
                 case
                   (all dead. Ordering)
                   (lessThanEqualsInteger x y)
                   [(/\dead -> GT), (/\dead -> LT)]
                   {all dead. dead})
            , (/\dead -> EQ) ]
            {all dead. dead}
  ~`$fOrdInteger_$cmax` : integer -> integer -> integer
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) ->
          let
            !y : integer = y
          in
          case
            (all dead. integer)
            (lessThanEqualsInteger x y)
            [(/\dead -> x), (/\dead -> y)]
            {all dead. dead}
  ~`$fOrdInteger_$cmin` : integer -> integer -> integer
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) ->
          let
            !y : integer = y
          in
          case
            (all dead. integer)
            (lessThanEqualsInteger x y)
            [(/\dead -> y), (/\dead -> x)]
            {all dead. dead}
  ~equalsInteger : integer -> integer -> bool
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in equalsInteger x y
  !ifThenElse : all a. bool -> a -> a -> a
    = /\a -> \(b : bool) (x : a) (y : a) -> case a b [y, x]
  !lessThanInteger : integer -> integer -> bool = lessThanInteger
  ~greaterThanEqualsInteger : integer -> integer -> bool
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) ->
          let
            !y : integer = y
          in
          ifThenElse {bool} (lessThanInteger x y) False True
  ~greaterThanInteger : integer -> integer -> bool
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) ->
          let
            !y : integer = y
          in
          ifThenElse {bool} (lessThanEqualsInteger x y) False True
  ~lessThanEqualsInteger : integer -> integer -> bool
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in lessThanEqualsInteger x y
  ~lessThanInteger : integer -> integer -> bool
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) -> let !y : integer = y in lessThanInteger x y
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
  ~`$fOrdInteger` : Ord integer
    = CConsOrd
        {integer}
        equalsInteger
        `$fOrdInteger_$ccompare`
        lessThanInteger
        lessThanEqualsInteger
        greaterThanInteger
        greaterThanEqualsInteger
        `$fOrdInteger_$cmax`
        `$fOrdInteger_$cmin`
  ~compare : all a. Ord a -> a -> a -> Ordering
    = /\a ->
        \(v : Ord a) ->
          Ord_match
            {a}
            v
            {a -> a -> Ordering}
            (\(v : (\a -> a -> a -> bool) a)
              (v : a -> a -> Ordering)
              (v : a -> a -> bool)
              (v : a -> a -> bool)
              (v : a -> a -> bool)
              (v : a -> a -> bool)
              (v : a -> a -> a)
              (v : a -> a -> a) ->
               v)
  ~opCompare : all a. Ord a -> a -> a -> Ordering
    = /\a ->
        \(`$dOrd` : Ord a) (a : a) ->
          let
            !a : a = a
          in
          \(b : a) ->
            let
              !b : a = b
            in
            Ordering_match
              (compare {a} `$dOrd` a b)
              {all dead. Ordering}
              (/\dead -> EQ)
              (/\dead -> LT)
              (/\dead -> GT)
              {all dead. dead}
in
opCompare {integer} `$fOrdInteger` 1 2