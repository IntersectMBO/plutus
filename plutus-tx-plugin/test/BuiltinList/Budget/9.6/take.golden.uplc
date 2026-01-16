(program
   1.1.0
   ((\take xs -> force (force take) [] 5 xs)
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