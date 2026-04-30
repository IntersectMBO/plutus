(program
   1.1.0
   ((\s ->
       s
         s
         ((\s -> case (constr 0 [s, 1, 1000]) [s])
            (\s x lim ->
               case
                 (lessThanEqualsInteger x lim)
                 [ (constr 0 [])
                 , (constr 1
                      [ x
                      , ((\x -> case (constr 0 [s, x, lim]) [s])
                           (addInteger 1 x)) ]) ])))
      (\s ds -> case ds [0, (\x xs -> addInteger x (s s xs))])))