(program
   1.1.0
   ((\forced ->
       (\go ds -> go 10)
         ((\s -> s s)
            (\s n ->
               case
                 (lessThanEqualsInteger n 0)
                 [(forced 0 ((\x -> s s x) (subtractInteger n 1))), []])))
      (force mkCons)))