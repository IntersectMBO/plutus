(program
   1.1.0
   (\xs ->
      force
        ((\f ->
            (\s -> f (\x -> f (\x -> f (\x -> f (\x -> s s x) x) x) x))
              (\s -> f (\x -> s s x)))
           (\go arg ->
              delay
                (\l xs ->
                   case
                     l
                     [ (\y ys ->
                          case
                            (force
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
                                       (\xs ->
                                          case
                                            xs
                                            [ (\x xs ->
                                                 case
                                                   (lessThanEqualsInteger x y)
                                                   [ (force
                                                        (go (delay (\x -> x)))
                                                        xs)
                                                   , True ])
                                            , False ]))
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