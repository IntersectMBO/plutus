(program
   1.1.0
   ((\forced d ->
       case
         (case (unConstrData d) [(\l r -> r)])
         [ (\ds ds ->
              case
                ds
                [ (\ds ds ->
                     case
                       ds
                       [ (\ds ds ->
                            (\x ->
                               (\y ->
                                  (\z ->
                                     (\w ->
                                        addInteger
                                          (addInteger
                                             (addInteger
                                                (addInteger (addInteger x y) z)
                                                w)
                                             (case
                                                (lessThanInteger
                                                   (addInteger y z)
                                                   (addInteger x w))
                                                [ (addInteger y w)
                                                , (addInteger x z) ]))
                                          (case
                                             (lessThanInteger
                                                (addInteger z y)
                                                (addInteger w x))
                                             [ (addInteger w y)
                                             , (addInteger z x) ]))
                                       (unIData (forced ds)))
                                    (unIData ds))
                                 (unIData ds))
                              (unIData ds)) ]) ]) ])
      (force headList)))