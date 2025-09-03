(program
   1.1.0
   (\xs ->
      force
        ((\f ->
            (\s -> f (\x -> f (\x -> f (\x -> f (\x -> s s x) x) x) x))
              (\s -> f (\x -> s s x)))
           (\go arg ->
              delay
                (\i xs ->
                   case
                     xs
                     [ (\x xs ->
                          case
                            (equalsInteger x 4)
                            [ (force (go (delay (\x -> x))) (addInteger i 1) xs)
                            , (constr 0 [i]) ])
                     , (constr 1 []) ]))
           (delay (\x -> x)))
        0
        xs))