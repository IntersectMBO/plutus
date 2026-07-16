(program
   1.1.0
   ((\multiIndexArray -> force multiIndexArray)
      multiIndexArray
      [2,0,0,1]
      ((\unitval ->
          (\mkNilData ->
             (\mkI ->
                (\mkCons ->
                   (\listToArray ->
                      force listToArray
                        (force mkCons
                           (mkI 1)
                           (force mkCons
                              (mkI 2)
                              (force mkCons (mkI 3) (mkNilData unitval)))))
                     listToArray)
                  mkCons)
               iData)
            mkNilData)
         ())))