(program
   1.1.0
   ((\forced ->
       (\take xs -> case (constr 0 [[], 5, xs]) [(force take)])
         ((\s -> s s (delay (\x -> x)))
            (\s arg ->
               delay
                 (\`$dMkNil` n l ->
                    case
                      (lessThanEqualsInteger n 0)
                      [ (case
                           l
                           [ (\x xs ->
                                forced
                                  x
                                  (case
                                     (constr 0
                                        [`$dMkNil`, (subtractInteger n 1), xs])
                                     [(force (s s (delay (\x -> x))))]))
                           , `$dMkNil` ])
                      , `$dMkNil` ]))))
      (force mkCons)))