(program
   1.1.0
   (\l ->
      (\cse -> cse cse)
        (\s xs ->
           case
             xs
             [ (\h t ->
                  case
                    (s s t)
                    [ (\ipv ipv ->
                         case
                           (lessThanInteger (unIData h) 8)
                           [ (constr 0 [(force mkCons h ipv), ipv])
                           , (constr 0 [ipv, (force mkCons h ipv)]) ]) ])
             , (constr 0 [[], []]) ])
        l))