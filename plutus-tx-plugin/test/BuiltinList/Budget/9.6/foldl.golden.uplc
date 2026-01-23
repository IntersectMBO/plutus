(program
   1.1.0
   ((\go xs -> go 1 xs)
      ((\cse -> cse cse)
         (\s acc xs ->
            case
              xs
              [(\x xs -> (\x -> s s x) (multiplyInteger acc x) xs), acc]))))