(program
   1.2.0
   ((\forced forced xs ->
       case
         (forced 10 xs)
         [(\x xs ds _ann -> x), (\_ann -> (\x -> error) (forced "PT22" ()))]
         ()
         ())
      (force trace)
      (force dropList)))