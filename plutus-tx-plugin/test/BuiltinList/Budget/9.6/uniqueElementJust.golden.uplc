(program
   1.1.0
   ((\take xs ->
       case
         (force take [] 1 xs)
         [ (\x xs -> case xs [(\ds ds -> constr 1 []), (constr 0 [x])])
         , (constr 1 []) ])
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