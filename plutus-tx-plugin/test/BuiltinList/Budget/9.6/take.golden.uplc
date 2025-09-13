(program
   1.1.0
   ((\take xs -> force (force take) [] 5 xs)
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
                                  (force (force (take (delay (\x -> x))))
                                     `$dMkNil`
                                     (subtractInteger n 1)
                                     xs))
                           , `$dMkNil` ])
                      , `$dMkNil` ])))
         (delay (\x -> x)))))