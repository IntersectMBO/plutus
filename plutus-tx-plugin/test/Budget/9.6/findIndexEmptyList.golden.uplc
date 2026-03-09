(program
   1.1.0
   (case
      (constr 0
         [ (\s i ds ->
              case
                ds
                [ (constr 1 [])
                , (\x xs ->
                     case
                       (lessThanEqualsInteger 1 x)
                       [(constr 0 [i]), ((\x -> s s x) (addInteger 1 i) xs)]) ])
         , 0
         , (constr 0 []) ])
      [(\s -> s s)]))