(program
   1.1.0
   ((\goInner ->
       (\goOuter bd ->
          goOuter (unMapData bd))
         ((\s ->
             s s)
            (\s
              list ->
               case
                 list
                 [ (\hd ->
                      case
                        (equalsByteString
                           #706f6c6963795f30325f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f
                           (unBData (case hd [(\l r -> l)])))
                        [ (\x -> s s x)
                        , (\ds ->
                             goInner (unMapData (case hd [(\l r -> r)]))) ])
                 , 0 ])))
      ((\s ->
          s s)
         (\s
           list ->
            case
              list
              [ (\hd ->
                   case
                     (equalsByteString
                        #746f6b656e5f30325f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f
                        (unBData (case hd [(\l r -> l)])))
                     [(\x -> s s x), (\ds -> unIData (case hd [(\l r -> r)]))])
              , 0 ]))))