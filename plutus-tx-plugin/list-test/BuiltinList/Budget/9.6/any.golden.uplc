(program
   1.1.0
   (\xs ->
      (\any ->
         constr 0
           [ (any (\v -> case (lessThanInteger v 8) [True, False]) xs)
           , (any (\v -> case (lessThanInteger v 12) [True, False]) xs) ])
        (\p ->
           (\s -> s s)
             (\s xs ->
                case xs [(\x xs -> case (p x) [(s s xs), True]), False]))))