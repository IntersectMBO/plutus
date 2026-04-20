(program
   1.1.0
   ((\go xs -> go 1 xs)
      ((\s -> s s)
         (\s acc xs ->
            case
              xs
              [ (\x xs ->
                   (\x -> case (constr 0 [s, x, xs]) [s])
                     (multiplyInteger acc x))
              , acc ]))))