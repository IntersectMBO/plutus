(program
   1.1.0
   (\d ->
      (\l ->
         (\l ->
            (\l ->
               (\x ->
                  (\y ->
                     (\z ->
                        (\w ->
                           addInteger
                             (addInteger
                                (addInteger (addInteger (addInteger x y) z) w)
                                (case
                                   (lessThanInteger
                                      (addInteger y z)
                                      (addInteger x w))
                                   [(addInteger y w), (addInteger x z)]))
                             (case
                                (lessThanInteger
                                   (addInteger z y)
                                   (addInteger w x))
                                [(addInteger w y), (addInteger z x)]))
                          (unIData (force headList (force tailList l))))
                       (unIData (force headList l)))
                    (unIData (force headList l)))
                 (unIData (force headList l)))
              (force tailList l))
           (force tailList l))
        (case (unConstrData d) [(\l r -> r)])))