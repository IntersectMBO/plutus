(program
   1.1.0
   ((\go xs -> case (go xs) [True, False])
      ((\s -> s s)
         (\s xs ->
            case
              xs
              [(\x xs -> case (equalsInteger 42 x) [(s s xs), True]), False]))))