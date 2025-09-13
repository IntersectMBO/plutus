(program
   1.1.0
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
      ()))