(program
   1.1.0
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
                        force mkCons
                          (addInteger x 1)
                          (force (go (delay (\x -> x))) xs))
                   , [] ]))
         (delay (\x -> x)))))