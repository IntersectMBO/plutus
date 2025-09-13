(program
   1.1.0
   (\x y z ->
      (\cons ->
         (\f g x -> f (g x))
           (cons (\i -> iData i) x)
           ((\f g x -> f (g x))
              (cons (\i -> iData i) y)
              (cons (\i -> iData i) z)))
        (\`$dToData` h eta -> force mkCons (`$dToData` h) eta)
        []))