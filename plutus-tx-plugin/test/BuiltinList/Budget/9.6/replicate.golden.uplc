(program
   1.1.0
   (\ds ->
      force
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
           (\go arg ->
              delay
                (\n ->
                   case
                     (lessThanEqualsInteger n 0)
                     [ (force mkCons
                          0
                          (force (go (delay (\x -> x))) (subtractInteger n 1)))
                     , [] ]))
           (delay (\x -> x)))
        10))