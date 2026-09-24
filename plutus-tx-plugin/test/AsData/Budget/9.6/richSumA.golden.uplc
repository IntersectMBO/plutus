(program
   1.1.0
   ((\forced forced d ->
       case
         d
         [ (\args -> case args [(\hd tl -> case tl [(\hd tl -> unIData hd)])])
         , (\args ->
              case
                (forced 2 args)
                [ (\hd tl ->
                     addInteger
                       (unIData hd)
                       (unIData (forced (forced 3 tl)))) ])
         , (\args ->
              case
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
                                        (unIData hd))) ]) ]) ]) ])
      (force headList)
      (force dropList)))