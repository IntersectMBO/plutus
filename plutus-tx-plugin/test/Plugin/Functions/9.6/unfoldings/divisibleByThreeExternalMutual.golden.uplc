(program
   1.1.0
   ((\fix1 ->
       (\subtractInteger ->
          (\equalsInteger ->
             (\tup ->
                (\divisibleByThreeDirect ->
                   (\divisibleByThreeDirect -> force divisibleByThreeDirect)
                     (divisibleByThreeDirect (delay (\x -> x))))
                  (force tup (\arg_0 -> arg_0)))
               (delay
                  (\f ->
                     f
                       (force
                          (force fix1)
                          (\divisibleByThreeDirect
                            arg ->
                             delay
                               (\n ->
                                  (\n ->
                                     force
                                       (case
                                          (equalsInteger n 0)
                                          [ (delay
                                               ((\n ->
                                                   (\n ->
                                                      force
                                                        (case
                                                           (equalsInteger n 0)
                                                           [ (delay
                                                                ((\n ->
                                                                    (\n ->
                                                                       force
                                                                         (case
                                                                            (equalsInteger
                                                                               n
                                                                               0)
                                                                            [ (delay
                                                                                 (force
                                                                                    (divisibleByThreeDirect
                                                                                       (delay
                                                                                          (\x ->
                                                                                             x)))
                                                                                    (subtractInteger
                                                                                       n
                                                                                       1)))
                                                                            , (delay
                                                                                 False) ]))
                                                                      n)
                                                                   (subtractInteger
                                                                      n
                                                                      1)))
                                                           , (delay False) ]))
                                                     n)
                                                  (subtractInteger n 1)))
                                          , (delay True) ]))
                                    n))))))
            equalsInteger)
         subtractInteger)
      (delay
         (delay
            (\f ->
               force (delay (\s -> s s))
                 (\s -> f (\x -> force (delay (\s -> s s)) s x)))))))