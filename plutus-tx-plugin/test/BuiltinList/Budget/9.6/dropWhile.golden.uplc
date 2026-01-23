(program
   1.1.0
   ((\go xs -> go xs)
      ((\cse -> cse cse)
         (\s xs ->
            case
              xs
              [(\x xs' -> case (lessThanInteger x 5) [xs, (s s xs')]), xs]))))