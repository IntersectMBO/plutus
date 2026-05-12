(program
   1.1.0
   (\xs ->
      (\any ->
         constr 0
           [ (any (\v -> lessThanEqualsInteger 8 v) xs)
           , (any (\v -> lessThanEqualsInteger 12 v) xs) ])
        (\p ->
           (\s -> s s)
             (\s xs ->
                case xs [(\x xs -> case (p x) [(s s xs), True]), False]))))