(program
   1.1.0
   ((\cse -> cse cse)
      (\s ds ->
         case
           ds
           [ 0
           , (\ds xs ->
                (\cse ->
                   cse
                     (case
                        xs
                        [ 0
                        , (\ds xs ->
                             cse (case xs [0, (\ds xs -> cse (s s xs))])) ]))
                  (addInteger 1)) ])))