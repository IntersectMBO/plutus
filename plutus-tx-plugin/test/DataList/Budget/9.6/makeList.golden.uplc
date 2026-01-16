(program
   1.1.0
   (\x y z ->
      (\cse ->
         (\f g x -> f (g x))
           (cse (\i -> iData i) x)
           ((\f g x -> f (g x))
              (cse (\i -> iData i) y)
              (cse (\i -> iData i) z)))
        (\`$dToData` h eta -> force mkCons (`$dToData` h) eta)
        []))