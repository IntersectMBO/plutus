(program
   1.1.0
   (\d ->
      case
        (unConstrData d)
        [ (\idx args ->
             case
               idx
               [ (case args [(\hd tl -> unIData hd)])
               , (case args [(\hd tl -> case tl [(\hd tl -> unIData hd)])])
               , (case
                    args
                    [ (\hd tl ->
                         case
                           tl
                           [ (\hd tl ->
                                case tl [(\hd tl -> unIData hd)]) ]) ]) ]) ]))