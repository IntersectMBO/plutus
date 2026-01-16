(program
   1.1.0
   ((\cse -> cse cse)
      (\s ds ->
         case
           ds
           [ True
           , (\x xs -> case (lessThanEqualsInteger x 0) [False, (s s xs)]) ])
      ((\cse -> cse cse)
         (\s n ->
            case
              (lessThanEqualsInteger n 0)
              [ (constr 1 [0, ((\x -> s s x) (subtractInteger n 1))])
              , (constr 0 []) ])
         1000)))