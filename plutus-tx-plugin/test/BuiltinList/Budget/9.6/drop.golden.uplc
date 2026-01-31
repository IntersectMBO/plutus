(program
   1.1.0
   ((\drop xs -> force drop [] 5 xs)
      ((\s -> s s)
         (\s arg ->
            delay
              (\`$dMkNil` n l ->
                 case
                   (lessThanEqualsInteger n 0)
                   [ (case
                        l
                        [ (\ds xs ->
                             force (s s (delay (\x -> x)))
                               `$dMkNil`
                               (subtractInteger n 1)
                               xs)
                        , `$dMkNil` ])
                   , l ]))
         (delay (\x -> x)))))