(program
   1.1.0
   ((\forced ->
       (\take xs ->
          case
            (case (constr 0 [[], 1, xs]) [(force take)])
            [ (\x xs -> case xs [(\ds ds -> constr 1 []), (constr 0 [x])])
            , (constr 1 []) ])
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