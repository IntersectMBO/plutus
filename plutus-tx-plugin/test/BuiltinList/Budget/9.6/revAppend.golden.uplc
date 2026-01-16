(program
   1.1.0
   ((\revAppend xs -> force (force revAppend) xs xs)
      ((\cse ->
          cse
            (\x ->
               cse
                 (\x ->
                    cse
                      (\x ->
                         (\cse -> cse (\x -> cse cse x) x)
                           (\s -> cse (\x -> s s x)))
                      x)
                 x))
         (\revAppend arg ->
            delay
              (delay
                 (\l r ->
                    case
                      l
                      [ (\x xs ->
                           force (force (revAppend (delay (\x -> x))))
                             xs
                             (force mkCons x r))
                      , r ])))
         (delay (\x -> x)))))