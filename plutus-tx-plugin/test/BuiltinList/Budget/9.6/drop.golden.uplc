(program
   1.1.0
   ((\drop xs -> force (force drop) [] 5 xs)
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