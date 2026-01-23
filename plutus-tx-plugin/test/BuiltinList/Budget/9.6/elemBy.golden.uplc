(program
   1.1.0
   ((\go xs -> go xs)
      ((\cse -> cse cse)
         (\s xs ->
            case
              xs
              [ (\x xs -> case (lessThanEqualsInteger x 0) [(s s xs), True])
              , False ]))))