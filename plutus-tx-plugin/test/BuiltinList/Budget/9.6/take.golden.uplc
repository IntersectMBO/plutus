(program
   1.1.0
   ((\take xs -> force take [] 5 xs)
      ((\s -> s s)
         (\s arg ->
            delay
              (\`$dMkNil` n l ->
                 case
                   (lessThanEqualsInteger n 0)
                   [ (case
                        l
                        [ (\x xs ->
                             force mkCons
                               x
                               (force (s s (delay (\x -> x)))
                                  `$dMkNil`
                                  (subtractInteger n 1)
                                  xs))
                        , `$dMkNil` ])
                   , `$dMkNil` ]))
         (delay (\x -> x)))))