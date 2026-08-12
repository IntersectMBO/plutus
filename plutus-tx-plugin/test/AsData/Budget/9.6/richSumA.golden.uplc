(program
   1.1.0
   ((\forced forced d ->
       case
         (unConstrData d)
         [ (\idx args ->
              case
                idx
                [ (case args [(\hd tl -> case tl [(\hd tl -> unIData hd)])])
                , (case
                     (forced 2 args)
                     [ (\hd tl ->
                          addInteger
                            (unIData hd)
                            (unIData (forced (forced 3 tl)))) ])
                , (case
                     (forced 3 args)
                     [ (\hd tl ->
                          case
                            (forced 4 tl)
                            [ (\hd tl ->
                                 case
                                   (forced 4 tl)
                                   [ (\hd tl ->
                                        addInteger
                                          (unIData hd)
                                          (addInteger
                                             (unIData hd)
                                             (unIData hd))) ]) ]) ]) ]) ])
      (force headList)
      (force dropList)))