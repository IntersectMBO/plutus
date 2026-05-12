(program
   1.1.0
   ((\forced forced d ->
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
                           (unIData (forced (forced l))))
                        (unIData (forced l)))
                     (unIData (forced l)))
                  (unIData (forced l)))
               (forced l))
            (forced l))
         (case (unConstrData d) [(\l r -> r)]))
      (force tailList)
      (force headList)))