(program
   1.1.0
   ((\drop xs -> case (constr 0 [[], 5, xs]) [(force (force drop))])
      ((\f ->
          (\s -> f (\x -> f (\x -> f (\x -> f (\x -> s s x) x) x) x))
            (\s -> f (\x -> s s x)))
         (\drop arg ->
            delay
              (delay
                 (\`$dMkNil` n l ->
                    case
                      (lessThanEqualsInteger n 0)
                      [ (case
                           l
                           [ (\ds xs ->
                                case
                                  (constr 0
                                     [`$dMkNil`, (subtractInteger n 1), xs])
                                  [(force (force (drop (delay (\x -> x)))))])
                           , `$dMkNil` ])
                      , l ])))
         (delay (\x -> x)))))