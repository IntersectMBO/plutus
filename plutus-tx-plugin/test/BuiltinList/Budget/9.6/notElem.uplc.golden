(program
   1.1.0
   (\xs ->
      case
        (force
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
                               (equalsInteger 42 x)
                               [(force (go (delay (\x -> x))) xs), True])
                        , False ]))
              (delay (\x -> x)))
           xs)
        [True, False]))