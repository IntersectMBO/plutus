(program
   1.1.0
   ((\go eta -> go eta)
      ((\cse -> cse cse)
         (\s xs ->
            case
              xs
              [(\h t -> case (equalsData (I 8) h) [(s s t), True]), False]))))