(program
   1.1.0
   ((\cse -> cse cse)
      (\s ds ->
         case
           ds
           [True, (\x xs -> case (lessThanInteger x 0) [(s s xs), False])])
      ((\cse -> cse cse)
         (\s n ->
            case
              (lessThanEqualsInteger n 0)
              [ (constr 1 [0, ((\x -> s s x) (subtractInteger n 1))])
              , (constr 0 []) ])
         1000)))