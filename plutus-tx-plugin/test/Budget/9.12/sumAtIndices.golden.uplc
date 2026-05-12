(program
   1.1.0
   ((\forced forced d ->
       (\nt ->
          (\s ->
             (\nt ->
                (\s ->
                   (\s -> addInteger (addInteger s s) s)
                     (unIData (forced (forced nt))))
                  (unIData (forced nt)))
               (forced (forced (forced nt))))
            (unIData (forced nt)))
         (forced (unListData d)))
      (force tailList)
      (force headList)))