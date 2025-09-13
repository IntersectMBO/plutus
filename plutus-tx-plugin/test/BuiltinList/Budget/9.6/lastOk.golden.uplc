(program
   1.1.0
   ((\last xs -> force (force last) xs)
      ((\f ->
          (\s -> f (\x -> f (\x -> f (\x -> f (\x -> s s x) x) x) x))
            (\s -> f (\x -> s s x)))
         (\last arg ->
            delay
              (delay
                 (\eta ->
                    case
                      eta
                      [ (\x xs ds ->
                           case
                             xs
                             [ (\ds ds ->
                                  force (force (last (delay (\x -> x)))) xs)
                             , x ])
                      , (\ds ->
                           (\x -> error) (force trace "PT25" (constr 0 []))) ]
                      (constr 0 []))))
         (delay (\x -> x)))))