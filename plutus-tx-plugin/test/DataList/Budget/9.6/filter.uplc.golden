(program
   1.1.0
   ((\go eta -> go eta)
      ((\s -> s s)
         (\s ds ->
            case
              ds
              [ (\x eta ->
                   (\h ->
                      case
                        (lessThanInteger h 8)
                        [ ((\nt -> force mkCons (iData h) nt) (s s eta))
                        , (s s eta) ])
                     (unIData x))
              , [] ]))))