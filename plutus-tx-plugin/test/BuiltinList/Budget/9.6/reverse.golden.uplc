(program
   1.1.0
   ((\revAppend xs -> force (force revAppend) xs [])
      ((\f ->
          (\s -> f (\x -> f (\x -> f (\x -> f (\x -> s s x) x) x) x))
            (\s -> f (\x -> s s x)))
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