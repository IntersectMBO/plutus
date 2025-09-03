(program
   1.1.0
   (\xs ->
      (\cse ->
         constr 0
           [ (cse (\v -> case (lessThanInteger v 8) [True, False]) xs)
           , (cse (\v -> case (lessThanInteger v 12) [True, False]) xs) ])
        (\p ->
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
                                 (p x)
                                 [(force (go (delay (\x -> x))) xs), True])
                          , False ]))
                (delay (\x -> x))))))