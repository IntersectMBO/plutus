(program
   1.1.0
   (\ds ->
      force
        ((\f ->
            (\s -> f (\x -> f (\x -> f (\x -> f (\x -> s s x) x) x) x))
              (\s -> f (\x -> s s x)))
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