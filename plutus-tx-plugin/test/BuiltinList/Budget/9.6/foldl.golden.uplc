(program
   1.1.0
   (\xs ->
      force
        ((\f ->
            (\s -> f (\x -> f (\x -> f (\x -> f (\x -> s s x) x) x) x))
              (\s -> f (\x -> s s x)))
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