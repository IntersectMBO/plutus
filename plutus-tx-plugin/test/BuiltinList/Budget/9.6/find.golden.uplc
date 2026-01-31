(program
   1.1.0
   (\xs ->
      (\find ->
         constr 0
           [ (find (\v -> case (lessThanInteger v 8) [True, False]) xs)
           , (find (\v -> case (lessThanInteger v 12) [True, False]) xs) ])
        (\p ->
           (\s -> s s)
             (\s xs ->
                case
                  xs
                  [ (\x xs -> case (p x) [(s s xs), (constr 0 [x])])
                  , (constr 1 []) ]))))