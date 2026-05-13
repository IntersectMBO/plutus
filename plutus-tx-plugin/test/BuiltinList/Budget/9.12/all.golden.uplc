(program
   1.1.0
   (\xs ->
      (\all ->
         constr 0
           [ (all (\v -> lessThanEqualsInteger 8 v) xs)
           , (all (\v -> lessThanEqualsInteger 0 v) xs) ])
        (\p ->
           (\s -> s s)
             (\s xs ->
                case xs [(\x xs -> case (p x) [False, (s s xs)]), True]))))