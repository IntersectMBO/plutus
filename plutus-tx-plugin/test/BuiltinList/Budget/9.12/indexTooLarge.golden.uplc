(program
   1.1.0
   ((\forced forced xs ->
       case
         (forced 10 xs)
         [ (\x xs ds _ann -> x)
         , (\_ann -> (\x -> error) (forced "PT22" (constr 0 []))) ]
         (constr 0 [])
         (constr 0 []))
      (force trace)
      (force dropList)))