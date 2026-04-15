(program
   1.1.0
   (\bd ->
      (\nt ->
         (\`$j` ->
            case
              (case nt [(\x eta -> constr 0 [x]), (constr 1 [])])
              [ (\arg ->
                   (\ds -> force `$j`) (constrData 0 (force mkCons arg [])))
              , (force `$j`) ])
           (delay
              (case
                 (case nt [(\x eta -> constr 0 [x]), (constr 1 [])])
                 [ (\arg -> (\ds -> ()) (constrData 0 (force mkCons arg [])))
                 , () ])))
        (unListData bd)))