(program
   1.1.0
   (\d ->
      (\cse ->
         (\cse ->
            (\cse ->
               (\s ->
                  (\cse ->
                     (\s ->
                        (\s -> addInteger (addInteger s s) s)
                          (unIData (cse (cse cse))))
                       (unIData (cse cse)))
                    (cse (cse (cse cse))))
                 (unIData (cse cse)))
              (cse (unListData d)))
           (force headList))
        (force tailList)))