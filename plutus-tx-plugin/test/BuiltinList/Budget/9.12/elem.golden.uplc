(program
   1.1.0
   (\xs ->
      (\elem ->
         constr 0
           [ (elem (\x y -> equalsInteger x y) 8 xs)
           , (elem (\x y -> equalsInteger x y) 12 xs) ])
        (\`$dEq` a ->
           (\s -> s s)
             (\s xs ->
                case
                  xs
                  [(\x xs -> case (`$dEq` a x) [(s s xs), True]), False]))))