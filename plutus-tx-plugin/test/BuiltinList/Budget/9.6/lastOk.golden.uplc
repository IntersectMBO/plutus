(program
   1.1.0
   ((\forced ->
       (\last xs -> force last xs)
         ((\s -> s s (delay (\x -> x)))
            (\s arg ->
               delay
                 (\eta ->
                    case
                      eta
                      [ (\x xs ds ->
                           case
                             xs
                             [(\ds ds -> force (s s (delay (\x -> x))) xs), x])
                      , (\ds -> (\x -> error) (forced "PT25" (constr 0 []))) ]
                      (constr 0 [])))))
      (force trace)))