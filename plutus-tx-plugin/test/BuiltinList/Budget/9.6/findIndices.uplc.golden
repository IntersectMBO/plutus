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
                          (\indices ->
                             case
                               (equalsInteger (modInteger x 2) 0)
                               [(force mkCons i indices), indices])
                            (force (go (delay (\x -> x))) (addInteger i 1) xs))
                     , [] ]))
           (delay (\x -> x)))
        0
        xs))