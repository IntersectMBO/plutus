(program
   1.1.0
   (\xs ->
      (\cse ->
         constr 0
           [ (cse (\v -> case (lessThanInteger v 8) [True, False]) xs)
           , (cse (\v -> case (lessThanInteger v 0) [True, False]) xs) ])
        (\p ->
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
                                 (p x)
                                 [False, (force (go (delay (\x -> x))) xs)])
                          , True ]))
                (delay (\x -> x))))))