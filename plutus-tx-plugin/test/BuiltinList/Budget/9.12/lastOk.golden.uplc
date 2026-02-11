(program
   1.1.0
   ((\last xs -> force last xs)
      ((\s -> s s)
         (\s arg ->
            delay
              (\eta ->
                 case
                   eta
                   [ (\x xs ds ->
                        case
                          xs
                          [(\ds ds -> force (s s (delay (\x -> x))) xs), x])
                   , (\ds -> (\x -> error) (force trace "PT25" (constr 0 []))) ]
                   (constr 0 [])))
         (delay (\x -> x)))))