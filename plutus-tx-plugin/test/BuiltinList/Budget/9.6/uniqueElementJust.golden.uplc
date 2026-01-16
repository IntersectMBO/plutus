(program
   1.1.0
   ((\take xs ->
       case
         (force (force take) [] 1 xs)
         [ (\x ->
              (\z f xs -> case xs [f, z])
                (constr 0 [x])
                (\ds ds -> constr 1 []))
         , (constr 1 []) ])
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