(program
   1.1.0
   (\v ->
      (\l ->
         force
           (force (force chooseList)
              l
              (delay
                 (\_ann -> (\x -> error) (force trace "PT22" (constr 0 []))))
              (delay
                 ((\x xs ds eta -> x) (force headList l) (force tailList l))))
           (constr 0 [])
           (constr 0 []))
        (force dropList 20 v)))