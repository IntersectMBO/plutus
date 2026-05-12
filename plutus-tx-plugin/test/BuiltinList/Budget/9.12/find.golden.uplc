(program
   1.1.0
   (\xs ->
      (\find ->
         constr 0
           [ (find (\v -> lessThanEqualsInteger 8 v) xs)
           , (find (\v -> lessThanEqualsInteger 12 v) xs) ])
        (\p ->
           (\s -> s s)
             (\s xs ->
                case
                  xs
                  [ (\x xs -> case (p x) [(s s xs), (constr 0 [x])])
                  , (constr 1 []) ]))))