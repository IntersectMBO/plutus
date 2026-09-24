(program
   1.2.0
   ((\go xs -> go xs)
      ((\s -> s s)
         (\s xs ->
            case
              xs
              [(\x xs' -> case (lessThanInteger x 5) [xs, (s s xs')]), xs]))))