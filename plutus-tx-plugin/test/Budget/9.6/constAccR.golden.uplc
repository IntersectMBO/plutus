(program
   1.1.0
   ((\cse -> cse cse)
      (\s ds -> case ds [42, (\x xs -> s s xs)])
      ((\cse -> cse cse)
         (\s n ->
            case
              (lessThanEqualsInteger n 0)
              [ (constr 1 [1, ((\x -> s s x) (subtractInteger n 1))])
              , (constr 0 []) ])
         1000)))