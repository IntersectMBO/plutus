(program
   1.1.0
   ((\go xs -> go xs xs)
      ((\cse -> cse cse)
         (\s xs ys ->
            case
              xs
              [ (\x xs' ->
                   case
                     ys
                     [ (\y ys' -> force mkCons (addInteger x y) (s s xs' ys'))
                     , [] ])
              , [] ]))))