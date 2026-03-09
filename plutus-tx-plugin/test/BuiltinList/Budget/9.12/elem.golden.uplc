(program
   1.1.0
   (\xs ->
      (\elem ->
         constr 0
           [ (case (constr 0 [(\x y -> equalsInteger x y), 8, xs]) [elem])
           , (case (constr 0 [(\x y -> equalsInteger x y), 12, xs]) [elem]) ])
        (\`$dEq` a ->
           (\s -> s s)
             (\s xs ->
                case
                  xs
                  [(\x xs -> case (`$dEq` a x) [(s s xs), True]), False]))))