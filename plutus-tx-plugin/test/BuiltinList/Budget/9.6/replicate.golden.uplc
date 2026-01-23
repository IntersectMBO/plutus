(program
   1.1.0
   ((\go ds -> go 10)
      ((\cse -> cse cse)
         (\s n ->
            case
              (lessThanEqualsInteger n 0)
              [(force mkCons 0 ((\x -> s s x) (subtractInteger n 1))), []]))))