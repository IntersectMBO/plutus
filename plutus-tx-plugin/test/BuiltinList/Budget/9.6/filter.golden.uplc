(program
   1.1.0
   (\xs ->
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
                          (\xs ->
                             case
                               (equalsInteger (modInteger x 2) 0)
                               [xs, (force mkCons x xs)])
                            (force (go (delay (\x -> x))) xs))
                     , [] ]))
           (delay (\x -> x)))
        xs))