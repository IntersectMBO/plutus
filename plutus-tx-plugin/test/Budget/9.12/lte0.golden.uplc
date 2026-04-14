(program
   1.1.0
   ((\s ->
       s
         s
         ((\s -> s s 1000)
            (\s n ->
               case
                 (lessThanEqualsInteger n 0)
                 [ (constr 1 [0, ((\x -> s s x) (subtractInteger n 1))])
                 , (constr 0 []) ])))
      (\s ds ->
         case
           ds
           [ True
           , (\x xs -> case (lessThanEqualsInteger x 0) [False, (s s xs)]) ])))