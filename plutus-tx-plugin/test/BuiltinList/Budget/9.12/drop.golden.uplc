(program
   1.1.0
   ((\drop xs -> case (constr 0 [[], 5, xs]) [(force drop)])
      ((\s -> s s (delay (\x -> x)))
         (\s arg ->
            delay
              (\`$dMkNil` n l ->
                 case
                   (lessThanEqualsInteger n 0)
                   [ (case
                        l
                        [ (\ds xs ->
                             case
                               (constr 0 [`$dMkNil`, (subtractInteger n 1), xs])
                               [(force (s s (delay (\x -> x))))])
                        , `$dMkNil` ])
                   , l ])))))