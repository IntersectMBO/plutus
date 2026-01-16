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
                (\acc xs ->
                   case
                     xs
                     [ (\x xs ->
                          force (go (delay (\x -> x)))
                            (multiplyInteger acc x)
                            xs)
                     , acc ]))
           (delay (\x -> x)))
        1
        xs))