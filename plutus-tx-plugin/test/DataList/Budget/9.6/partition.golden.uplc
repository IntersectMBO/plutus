(program
   1.1.0
   ((\forced l ->
       (\s -> s s l)
         (\s xs ->
            case
              xs
              [ (\h t ->
                   case
                     (s s t)
                     [ (\ipv ipv ->
                          case
                            (lessThanInteger (unIData h) 8)
                            [ (constr 0 [(forced h ipv), ipv])
                            , (constr 0 [ipv, (forced h ipv)]) ]) ])
              , (constr 0 [[], []]) ]))
      (force mkCons)))