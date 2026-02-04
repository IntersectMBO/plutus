(program
   1.1.0
   (\xs ->
      (\caseList' ->
         (\eta ->
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
                                                      f
                                                        (\x ->
                                                           f (\x -> s s x) x)
                                                        x)
                                                   x))
                                           (\s -> f (\x -> s s x)))
                                        (\go arg ->
                                           delay
                                             (caseList'
                                                False
                                                (\x xs ->
                                                   case
                                                     (equalsInteger x y)
                                                     [ (force
                                                          (go (delay (\x -> x)))
                                                          xs)
                                                     , True ])))
                                        (delay (\x -> x)))
                                     xs)
                                  [ ((\cse ->
                                        cse
                                          (force (go (delay (\x -> x)))
                                             ys
                                             (cse xs)))
                                       (force mkCons y))
                                  , (force (go (delay (\x -> x))) ys xs) ])
                           , [] ]))
                 (delay (\x -> x)))
              eta
              [])
           (force
              ((\f ->
                  (\s -> f (\x -> f (\x -> f (\x -> f (\x -> s s x) x) x) x))
                    (\s -> f (\x -> s s x)))
                 (\go arg ->
                    delay
                      (caseList'
                         xs
                         (\x xs ->
                            force mkCons x (force (go (delay (\x -> x))) xs))))
                 (delay (\x -> x)))
              xs))
        (\z f xs -> case xs [f, z])))