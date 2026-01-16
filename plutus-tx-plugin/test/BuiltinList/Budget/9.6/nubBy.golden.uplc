(program
   1.1.0
   (\xs ->
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
                (\l xs ->
                   case
                     l
                     [ (\y ys ->
                          case
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
                                       ((\z f xs -> case xs [f, z])
                                          False
                                          (\x xs ->
                                             case
                                               (lessThanEqualsInteger x y)
                                               [ (force (go (delay (\x -> x)))
                                                    xs)
                                               , True ])))
                                  (delay (\x -> x)))
                               xs)
                            [ ((\cse ->
                                  cse
                                    (force (go (delay (\x -> x))) ys (cse xs)))
                                 (force mkCons y))
                            , (force (go (delay (\x -> x))) ys xs) ])
                     , [] ]))
           (delay (\x -> x)))
        xs
        []))