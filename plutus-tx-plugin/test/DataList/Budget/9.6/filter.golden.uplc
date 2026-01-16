(program
   1.1.0
   ((\go eta -> go eta)
      ((\cse -> cse cse)
         (\s ds ->
            case
              ds
              [ (\x eta ->
                   (\cse ->
                      case
                        (lessThanInteger cse 8)
                        [ ((\nt -> force mkCons (iData cse) nt) (s s eta))
                        , (s s eta) ])
                     (unIData x))
              , [] ]))))