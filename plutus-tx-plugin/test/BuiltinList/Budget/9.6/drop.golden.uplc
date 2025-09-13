(program
   1.1.0
   ((\drop xs -> force (force drop) [] 5 xs)
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
                                force (force (drop (delay (\x -> x))))
                                  `$dMkNil`
                                  (subtractInteger n 1)
                                  xs)
                           , `$dMkNil` ])
                      , l ])))
         (delay (\x -> x)))))