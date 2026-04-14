(program
   1.1.0
   ((\go ds -> go 10)
      ((\s -> s s)
         (\s n ->
            case
              (lessThanEqualsInteger n 0)
              [(force mkCons 0 ((\x -> s s x) (subtractInteger n 1))), []]))))