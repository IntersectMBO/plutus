(program
   1.1.0
   ((\go ->
       (\ls -> go 0 ls)
         ((\s -> case (constr 0 [s, 1, 1000]) [s])
            (\s x lim ->
               case
                 (lessThanInteger lim x)
                 [ (constr 1
                      [ x
                      , ((\x -> case (constr 0 [s, x, lim]) [s])
                           (addInteger 1 x)) ])
                 , (constr 0 []) ])))
      ((\s -> s s)
         (\s acc ds ->
            case
              ds
              [ acc
              , (\x xs ->
                   (\x -> case (constr 0 [s, x, xs]) [s])
                     (addInteger acc x)) ]))))