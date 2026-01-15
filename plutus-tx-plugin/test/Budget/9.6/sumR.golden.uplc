(program
   1.1.0
   ((\s -> s s)
      (\s ds -> case ds [0, (\x xs -> addInteger x (s s xs))])
      (case
         (constr 0
            [ (\s x lim ->
                 case
                   (lessThanEqualsInteger x lim)
                   [ (constr 0 [])
                   , (constr 1 [x, ((\x -> s s x) (addInteger 1 x) lim)]) ])
            , 1
            , 1000 ])
         [(\s -> s s)])))