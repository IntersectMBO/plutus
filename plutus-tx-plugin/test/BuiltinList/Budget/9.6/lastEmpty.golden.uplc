(program
   1.1.0
   ((\last ds -> force (force last) [])
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