(program
   1.1.0
   ((\forced input ->
       case
         (forced 3 (unListData input))
         [ (\hd tl ->
              case
                (forced 3 tl)
                [ (\hd tl ->
                     case
                       (forced 6 tl)
                       [ (\hd tl ->
                            addInteger
                              (unIData hd)
                              (addInteger (unIData hd) (unIData hd))) ]) ]) ])
      (force dropList)))