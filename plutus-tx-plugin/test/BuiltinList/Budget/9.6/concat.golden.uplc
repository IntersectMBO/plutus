(program
   1.1.0
   (\xss ->
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
                ((\cse ->
                    cse
                      []
                      (\x xs ->
                         (\acc ->
                            force
                              ((\cse ->
                                  cse
                                    (\x ->
                                       cse
                                         (\x ->
                                            cse
                                              (\x ->
                                                 (\cse ->
                                                    cse (\x -> cse cse x) x)
                                                   (\s -> cse (\x -> s s x)))
                                              x)
                                         x))
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