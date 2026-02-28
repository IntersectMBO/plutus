(program
   1.1.0
   (\d ->
      case
        ((\l -> constr 0 [(force headList l), (force tailList l)])
           (case (unConstrData d) [(\l r -> r)]))
        [ (\ds ds ->
             (\ds ->
                (\ds ->
                   (\ds ->
                      (\ds ->
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
                                          [(addInteger w y), (addInteger z x)]))
                                    (unIData (force headList ds)))
                                 (unIData ds))
                              (unIData ds))
                           (unIData ds))
                        (force tailList ds))
                     (force headList ds))
                  (force tailList ds))
               (force headList ds)) ]))