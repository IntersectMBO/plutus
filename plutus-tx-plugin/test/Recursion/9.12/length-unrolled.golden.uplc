(program
   1.2.0
   ((\s -> s s)
      (\s ds ->
         case
           ds
           [ 0
           , (\ds xs ->
                addInteger
                  1
                  (case
                     xs
                     [ 0
                     , (\ds xs ->
                          addInteger
                            1
                            (case
                               xs
                               [0, (\ds xs -> addInteger 1 (s s xs))])) ])) ])))