(program
   1.1.0
   (\bd ->
      (\m ->
         (\s ->
            case
              (s s m)
              [ (\a ->
                   (\m ->
                      (\s -> case (s s m) [(\a -> unIData a), 0])
                        (\s xs ->
                           case
                             xs
                             [ (\hd ->
                                  case
                                    (equalsData (B #) (case hd [(\l r -> l)]))
                                    [ (\x -> s s x)
                                    , (\ds ->
                                         constr 0 [(case hd [(\l r -> r)])]) ])
                             , (constr 1 []) ]))
                     (unMapData a))
              , 0 ])
           (\s xs ->
              case
                xs
                [ (\hd ->
                     case
                       (equalsData (B #) (case hd [(\l r -> l)]))
                       [ (\x -> s s x)
                       , (\ds -> constr 0 [(case hd [(\l r -> r)])]) ])
                , (constr 1 []) ]))
        (unMapData bd)))