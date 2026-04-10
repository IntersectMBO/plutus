(program
   1.1.0
   ((\revAppend xs -> force revAppend xs [])
      ((\s -> s s)
         (\s arg ->
            delay
              (\l r ->
                 case
                   l
                   [ (\x xs ->
                        force (s s (delay (\x -> x))) xs (force mkCons x r))
                   , r ]))
         (delay (\x -> x)))))