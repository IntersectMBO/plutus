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
                          case
                            (equalsInteger x 99)
                            [ (force (go (delay (\x -> x))) (addInteger i 1) xs)
                            , (constr 0 [i]) ])
                     , (constr 1 []) ]))
           (delay (\x -> x)))
        0
        xs))