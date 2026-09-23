(program
   1.1.0
   ((\fix1 ->
       (\subtractInteger ->
          (\subtractInteger ->
             (\equalsInteger ->
                (\equalsInteger ->
                   (\tup ->
                      (\even -> (\even -> force even) (even (delay (\x -> x))))
                        (force tup (\arg_0 -> arg_0)))
                     (delay
                        (\f ->
                           f
                             (force
                                (force fix1)
                                (\even
                                  arg ->
                                   delay
                                     (\n ->
                                        (\n ->
                                           force
                                             (case
                                                (force equalsInteger n 0)
                                                [ (delay
                                                     ((\n ->
                                                         force
                                                           (case
                                                              (force
                                                                 equalsInteger
                                                                 n
                                                                 0)
                                                              [ (delay
                                                                   (force
                                                                      (even
                                                                         (delay
                                                                            (\x ->
                                                                               x)))
                                                                      (force
                                                                         subtractInteger
                                                                         n
                                                                         1)))
                                                              , (delay
                                                                   False) ]))
                                                        (force subtractInteger
                                                           n
                                                           1)))
                                                , (delay True) ]))
                                          n))))))
                  (delay (\x -> (\x y -> (\y -> equalsInteger x y) y) x)))
               equalsInteger)
            (delay (\x -> (\x y -> (\y -> subtractInteger x y) y) x)))
         subtractInteger)
      (delay
         (delay
            (\f ->
               force (delay (\s -> s s))
                 (\s -> f (\x -> force (delay (\s -> s s)) s x)))))))