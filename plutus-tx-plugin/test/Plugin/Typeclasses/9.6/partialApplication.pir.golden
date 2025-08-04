let
  data Ordering | Ordering_match where
    EQ : Ordering
    GT : Ordering
    LT : Ordering
  !equalsInteger : integer -> integer -> bool = equalsInteger
  !lessThanEqualsInteger : integer -> integer -> bool = lessThanEqualsInteger
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
in
`$fOrdInteger_$ccompare`