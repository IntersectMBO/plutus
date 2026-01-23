(program
   1.1.0
   ((\go xs -> go 0 xs)
      ((\cse -> cse cse)
         (\s i xs ->
            case
              xs
              [ (\x xs ->
                   case
                     (equalsInteger 99 x)
                     [((\x -> s s x) (addInteger 1 i) xs), (constr 0 [i])])
              , (constr 1 []) ]))))