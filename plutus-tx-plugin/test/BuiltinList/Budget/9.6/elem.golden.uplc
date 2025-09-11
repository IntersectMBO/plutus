(program
   1.1.0
   (\xs ->
      (\cse -> constr 0 [(cse 8 xs), (cse 12 xs)])
        (\a ->
           force
             ((\f ->
                 (\s -> f (\x -> f (\x -> f (\x -> f (\x -> s s x) x) x) x))
                   (\s -> f (\x -> s s x)))
                (\go arg ->
                   delay
                     (\xs ->
                        case
                          xs
                          [ (\x xs ->
                               case
                                 (equalsInteger a x)
                                 [(force (go (delay (\x -> x))) xs), True])
                          , False ]))
                (delay (\x -> x))))))