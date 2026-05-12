(program
   1.1.0
   ((\forced ->
       (\revAppend xs -> force revAppend xs xs)
         ((\s -> s s (delay (\x -> x)))
            (\s arg ->
               delay
                 (\l r ->
                    case
                      l
                      [ (\x xs -> force (s s (delay (\x -> x))) xs (forced x r))
                      , r ]))))
      (force mkCons)))