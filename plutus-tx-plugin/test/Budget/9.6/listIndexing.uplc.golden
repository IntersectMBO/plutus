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
                     [((\x -> s s x) (subtractInteger ds 1) xs), x]) ]))))