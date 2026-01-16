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
                (\i xs ->
                   case
                     xs
                     [ (\x xs ->
                          (\indices ->
                             case
                               (equalsInteger (modInteger x 2) 0)
                               [(force mkCons i indices), indices])
                            (force (go (delay (\x -> x))) (addInteger i 1) xs))
                     , [] ]))
           (delay (\x -> x)))
        0
        xs))