(program
   1.1.0
   ((\go xs -> go 5 xs)
      ((\s -> s s)
         (\s ds ds ->
            case
              ds
              [ ((\x -> error) (force trace "PT7" (constr 0 [])))
              , (\x xs ->
                   case
                     (equalsInteger 0 ds)
                     [ ((\x -> case (constr 0 [s, x, xs]) [s])
                          (subtractInteger ds 1))
                     , x ]) ]))))