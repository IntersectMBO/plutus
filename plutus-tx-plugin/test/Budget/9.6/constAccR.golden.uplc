(program
   1.1.0
   ((\s -> s s)
      (\s ds -> case ds [42, (\x xs -> s s xs)])
      ((\s -> s s)
         (\s n ->
            case
              (lessThanEqualsInteger n 0)
              [ (constr 1 [1, ((\x -> s s x) (subtractInteger n 1))])
              , (constr 0 []) ])
         1000)))