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
                         (\ys ->
                            (\l ->
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
                                            ys
                                            (\x xs ->
                                               force mkCons
                                                 x
                                                 (force (go (delay (\x -> x)))
                                                    xs))))
                                    (delay (\x -> x)))
                                 l)
                              (force
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
                                         (\n ->
                                            case
                                              (lessThanEqualsInteger n 0)
                                              [ (force mkCons
                                                   x
                                                   (force (go (delay (\x -> x)))
                                                      (subtractInteger n 1)))
                                              , [] ]))
                                    (delay (\x -> x)))
                                 2))
                           (force (go (delay (\x -> x))) xs)))
                   (\z f xs -> case xs [f, z])))
           (delay (\x -> x)))
        xss))