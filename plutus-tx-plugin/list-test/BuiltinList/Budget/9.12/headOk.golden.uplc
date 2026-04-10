(program
   1.1.0
   (\xs ->
      case
        xs
        [ (\x xs ds -> x)
        , (\ds -> (\x -> error) (force trace "PT23" (constr 0 []))) ]
        (constr 0 [])))