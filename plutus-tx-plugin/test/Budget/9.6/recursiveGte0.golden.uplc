(program
   1.1.0
   ((\go ->
       (\recursiveAll ->
          (\ls ->
             force recursiveAll
               (\v -> case (lessThanInteger v 0) [True, False])
               ls)
            (go 1000))
         ((\cse -> cse cse)
            (\s arg ->
               delay
                 (\ds ds ->
                    case
                      ds
                      [ True
                      , (\x xs ->
                           case
                             (ds x)
                             [False, (force (s s (delay (\x -> x))) ds xs)]) ]))
            (delay (\x -> x))))
      ((\cse -> cse cse)
         (\s n ->
            case
              (lessThanEqualsInteger n 0)
              [ (constr 1 [0, ((\x -> s s x) (subtractInteger n 1))])
              , (constr 0 []) ]))))