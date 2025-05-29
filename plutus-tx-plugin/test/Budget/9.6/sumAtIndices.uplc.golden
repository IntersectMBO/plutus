(program
   1.1.0
   (\d ->
      (\nt ->
         (\s ->
            (\nt ->
               (\s ->
                  (\s -> addInteger (addInteger s s) s)
                    (unIData (force headList (force tailList nt))))
                 (unIData (force headList nt)))
              (force tailList (force tailList (force tailList nt))))
           (unIData (force headList nt)))
        (force tailList (unListData d))))