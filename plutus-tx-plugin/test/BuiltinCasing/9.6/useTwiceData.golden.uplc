(program
   1.1.0
   ((\forced bd ->
       (\nt ->
          (\`$j` ->
             case
               (case nt [(\x eta -> constr 0 [x]), (constr 1 [])])
               [ (\arg -> `$j` (constrData 0 (forced arg [])))
               , (`$j` (Constr 1 [])) ])
            (\ipv ->
               case
                 (case nt [(\x eta -> constr 0 [x]), (constr 1 [])])
                 [(\arg -> (\ds -> ()) (constrData 0 (forced arg []))), ()]))
         (unListData bd))
      (force mkCons)))