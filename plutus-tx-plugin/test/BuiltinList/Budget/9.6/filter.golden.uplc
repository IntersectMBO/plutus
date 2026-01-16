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
                (\xs ->
                   case
                     xs
                     [ (\x xs ->
                          (\xs ->
                             case
                               (equalsInteger (modInteger x 2) 0)
                               [xs, (force mkCons x xs)])
                            (force (go (delay (\x -> x))) xs))
                     , [] ]))
           (delay (\x -> x)))
        xs))