(program
   1.2.0
   ((\go eta -> go eta)
      ((\s -> s s)
         (\s xs ->
            case
              xs
              [(\h t -> case (equalsData (I 8) h) [(s s t), True]), False]))))