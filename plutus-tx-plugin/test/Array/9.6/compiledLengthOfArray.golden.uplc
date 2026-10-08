(program
   1.2.0
   ((\lengthOfArray -> force lengthOfArray)
      lengthOfArray
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