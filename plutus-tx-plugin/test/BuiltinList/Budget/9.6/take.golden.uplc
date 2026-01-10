(program
   1.1.0
   ((\take xs -> case (constr 0 [[], 5, xs]) [(force (force take))])
      ((\f ->
          (\s -> f (\x -> f (\x -> f (\x -> f (\x -> s s x) x) x) x))
            (\s -> f (\x -> s s x)))
         (\take arg ->
            delay
              (delay
                 (\`$dMkNil` n l ->
                    case
                      (lessThanEqualsInteger n 0)
                      [ (case
                           l
                           [ (\x xs ->
                                force mkCons
                                  x
                                  (case
                                     (constr 0
                                        [`$dMkNil`, (subtractInteger n 1), xs])
                                     [ (force
                                          (force (take (delay (\x -> x))))) ]))
                           , `$dMkNil` ])
                      , `$dMkNil` ])))
         (delay (\x -> x)))))