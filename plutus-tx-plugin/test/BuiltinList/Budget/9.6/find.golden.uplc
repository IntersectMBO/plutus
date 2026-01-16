(program
   1.1.0
   (\xs ->
      (\cse ->
         constr 0
           [ (cse (\v -> case (lessThanInteger v 8) [True, False]) xs)
           , (cse (\v -> case (lessThanInteger v 12) [True, False]) xs) ])
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
                                 [ (force (go (delay (\x -> x))) xs)
                                 , (constr 0 [x]) ])
                          , (constr 1 []) ]))
                (delay (\x -> x))))))