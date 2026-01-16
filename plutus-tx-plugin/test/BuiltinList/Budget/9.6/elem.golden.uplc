(program
   1.1.0
   (\xs ->
      (\cse -> constr 0 [(cse 8 xs), (cse 12 xs)])
        (\a ->
           force
             ((\cse ->
                 cse
                   (\x ->
                      cse
                        (\x ->
                           cse
                             (\x ->
                                (\cse -> cse (\x -> cse cse x) x)
                                  (\s -> cse (\x -> s s x)))
                             x)
                        x))
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