(program
   1.1.0
   (\xs ->
      (\all ->
         constr 0
           [ (all (\v -> case (lessThanInteger v 8) [True, False]) xs)
           , (all (\v -> case (lessThanInteger v 0) [True, False]) xs) ])
        (\p ->
           (\s -> s s)
             (\s xs ->
                case xs [(\x xs -> case (p x) [False, (s s xs)]), True]))))