(program
   1.1.0
   ((\forced ->
       (\go eta -> go eta)
         ((\s -> s s)
            (\s ds ->
               case
                 ds
                 [ (\x eta ->
                      (\h ->
                         case
                           (lessThanEqualsInteger 8 h)
                           [ (s s eta)
                           , ((\nt -> forced (iData h) nt) (s s eta)) ])
                        (unIData x))
                 , [] ])))
      (force mkCons)))