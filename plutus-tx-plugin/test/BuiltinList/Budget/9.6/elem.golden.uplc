(program
   1.1.0
   (\xs ->
      (\cse ->
         constr 0
           [ (cse (\x y -> equalsInteger x y) 8 xs)
           , (cse (\x y -> equalsInteger x y) 12 xs) ])
        (\`$dEq` a ->
           (\cse -> cse cse)
             (\s xs ->
                case
                  xs
                  [(\x xs -> case (`$dEq` a x) [(s s xs), True]), False]))))