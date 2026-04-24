(program
   1.1.0
   ((\goInner ->
       (\goOuter bd -> goOuter (unMapData bd))
         ((\s -> s s)
            (\s list ->
               case
                 list
                 [ (\hd ->
                      case
                        (equalsByteString # (unBData (case hd [(\l r -> l)])))
                        [ (\x -> s s x)
                        , (\ds ->
                             goInner (unMapData (case hd [(\l r -> r)]))) ])
                 , 0 ])))
      ((\s -> s s)
         (\s list ->
            case
              list
              [ (\hd ->
                   case
                     (equalsByteString # (unBData (case hd [(\l r -> l)])))
                     [(\x -> s s x), (\ds -> unIData (case hd [(\l r -> r)]))])
              , 0 ]))))