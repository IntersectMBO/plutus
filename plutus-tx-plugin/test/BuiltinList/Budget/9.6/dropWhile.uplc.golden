(program
   1.1.0
   (\xs ->
      force
        ((\f ->
            (\s -> f (\x -> f (\x -> f (\x -> f (\x -> s s x) x) x) x))
              (\s -> f (\x -> s s x)))
           (\go arg ->
              delay
                (\xs ->
                   case
                     xs
                     [ (\x xs' ->
                          case
                            (lessThanInteger x 5)
                            [xs, (force (go (delay (\x -> x))) xs')])
                     , xs ]))
           (delay (\x -> x)))
        xs))