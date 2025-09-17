(program
   1.1.0
   (\xss ->
      force
        ((\f ->
            (\s -> f (\x -> f (\x -> f (\x -> f (\x -> s s x) x) x) x))
              (\s -> f (\x -> s s x)))
           (\go arg ->
              delay
                ((\cse ->
                    cse
                      []
                      (\x xs ->
                         (\acc ->
                            force
                              ((\f ->
                                  (\s ->
                                     f
                                       (\x ->
                                          f
                                            (\x ->
                                               f (\x -> f (\x -> s s x) x) x)
                                            x))
                                    (\s -> f (\x -> s s x)))
                                 (\go arg ->
                                    delay
                                      (cse
                                         acc
                                         (\x xs ->
                                            force mkCons
                                              x
                                              (force (go (delay (\x -> x)))
                                                 xs))))
                                 (delay (\x -> x))))
                           (force (go (delay (\x -> x))) xs)
                           x))
                   (\z f xs -> case xs [f, z])))
           (delay (\x -> x)))
        xss))