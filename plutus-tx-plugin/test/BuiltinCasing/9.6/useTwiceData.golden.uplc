(program
   1.1.0
   ((\forced bd ->
       (\nt ->
          (\`$j` ->
             case
               (case nt [(\x eta -> constr 0 [x]), (constr 1 [])])
               [ (\arg -> (\ds -> force `$j`) (constrData 0 (forced arg [])))
               , (force `$j`) ])
            (delay
               (case
                  (case nt [(\x eta -> constr 0 [x]), (constr 1 [])])
                  [(\arg -> (\ds -> ()) (constrData 0 (forced arg []))), ()])))
         (unListData bd))
      (force mkCons)))