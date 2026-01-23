(program
   1.1.0
   ((\revAppend xs -> force revAppend xs xs)
      ((\cse -> cse cse)
         (\s arg ->
            delay
              (\l r ->
                 case
                   l
                   [ (\x xs ->
                        force (s s (delay (\x -> x))) xs (force mkCons x r))
                   , r ]))
         (delay (\x -> x)))))