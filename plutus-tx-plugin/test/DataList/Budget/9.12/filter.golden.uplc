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
                           (lessThanInteger h 8)
                           [ ((\nt -> forced (iData h) nt) (s s eta))
                           , (s s eta) ])
                        (unIData x))
                 , [] ])))
      (force mkCons)))