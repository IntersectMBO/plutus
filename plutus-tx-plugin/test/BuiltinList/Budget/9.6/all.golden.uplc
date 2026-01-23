(program
   1.1.0
   (\xs ->
      (\cse ->
         constr 0
           [ (cse (\v -> case (lessThanInteger v 8) [True, False]) xs)
           , (cse (\v -> case (lessThanInteger v 0) [True, False]) xs) ])
        (\p ->
           (\cse -> cse cse)
             (\s xs ->
                case xs [(\x xs -> case (p x) [False, (s s xs)]), True]))))