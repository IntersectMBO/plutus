(program
   1.1.0
   (\bd ->
      (\value ->
         (\lookup' ->
            case
              (lookup'
                 (B #706f6c6963795f30355f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f)
                 value)
              [ (\a ->
                   (\m ->
                      case
                        (lookup'
                           (B #746f6b656e5f30355f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f5f)
                           m)
                        [(\a -> unIData a), 0])
                     (unMapData a))
              , 0 ])
           (\k m ->
              (\s -> s s m)
                (\s xs ->
                   case
                     xs
                     [ (\hd ->
                          case
                            (equalsData k (case hd [(\l r -> l)]))
                            [ (\x -> s s x)
                            , (\ds -> constr 0 [(case hd [(\l r -> r)])]) ])
                     , (constr 1 []) ])))
        (unMapData bd)))