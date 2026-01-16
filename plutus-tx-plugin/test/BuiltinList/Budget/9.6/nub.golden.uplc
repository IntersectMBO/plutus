(program
   1.1.0
   (\xs ->
      (\caseList' ->
         (\eta ->
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
                                                           cse
                                                             (\x -> cse cse x)
                                                             x)
                                                          (\s ->
                                                             cse (\x -> s s x)))
                                                     x)
                                                x))
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
                      (caseList'
                         xs
                         (\x xs ->
                            force mkCons x (force (go (delay (\x -> x))) xs))))
                 (delay (\x -> x)))
              xs))
        (\z f xs -> case xs [f, z])))