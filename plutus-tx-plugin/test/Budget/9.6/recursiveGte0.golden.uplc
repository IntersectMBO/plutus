(program
   1.1.0
   ((\go ->
       (\recursiveAll ->
          (\ls ->
             force recursiveAll
               (\v -> case (lessThanInteger v 0) [True, False])
               ls)
            (go 1000))
         ((\s -> s s)
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
      ((\s -> s s)
         (\s n ->
            case
              (lessThanEqualsInteger n 0)
              [ (constr 1 [0, ((\x -> s s x) (subtractInteger n 1))])
              , (constr 0 []) ]))))