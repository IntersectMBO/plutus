(program
   1.1.0
   ((\goInner ->
       (\goOuter
         bd
         bd ->
          goOuter
            (unMapData
               ((\outer ->
                   (\caseList' ->
                      (\lookupKeyInMap ->
                         (\filterMissingOuter ->
                            (\goOuter ->
                               (\outer ->
                                  mapData
                                    ((\s -> s s (goOuter outer))
                                       (\s ->
                                          caseList'
                                            (filterMissingOuter outer outer)
                                            (\hd tl ->
                                               force mkCons hd (s s tl)))))
                                 (unMapData bd))
                              ((\s ->
                                  s s)
                                 (\s
                                   list ->
                                    case
                                      list
                                      [ (\hd
                                          tl ->
                                           force
                                             mkCons
                                             (mkPairData
                                                (case hd [(\l r -> l)])
                                                (case
                                                   (lookupKeyInMap
                                                      (case hd [(\l r -> l)])
                                                      outer)
                                                   [ (\inner2Data ->
                                                        (\i ->
                                                           (\goInner ->
                                                              (\i ->
                                                                 mapData
                                                                   ((\s ->
                                                                       s
                                                                         s
                                                                         (goInner
                                                                            i))
                                                                      (\s ->
                                                                         caseList'
                                                                           (filterMissingOuter
                                                                              i
                                                                              i)
                                                                           (\hd
                                                                             tl ->
                                                                              force
                                                                                mkCons
                                                                                hd
                                                                                (s
                                                                                   s
                                                                                   tl)))))
                                                                (unMapData
                                                                   (case
                                                                      hd
                                                                      [ (\l
                                                                          r ->
                                                                           r) ])))
                                                             ((\s ->
                                                                 s s)
                                                                (\s
                                                                  list ->
                                                                   case
                                                                     list
                                                                     [ (\hd
                                                                         tl ->
                                                                          force
                                                                            mkCons
                                                                            (mkPairData
                                                                               (case
                                                                                  hd
                                                                                  [ (\l
                                                                                      r ->
                                                                                       l) ])
                                                                               (iData
                                                                                  (case
                                                                                     (lookupKeyInMap
                                                                                        (case
                                                                                           hd
                                                                                           [ (\l
                                                                                               r ->
                                                                                                l) ])
                                                                                        i)
                                                                                     [ (\amt2Data ->
                                                                                          addInteger
                                                                                            (unIData
                                                                                               (case
                                                                                                  hd
                                                                                                  [ (\l
                                                                                                      r ->
                                                                                                       r) ]))
                                                                                            (unIData
                                                                                               amt2Data))
                                                                                     , (unIData
                                                                                          (case
                                                                                             hd
                                                                                             [ (\l
                                                                                                 r ->
                                                                                                  r) ])) ])))
                                                                            (s
                                                                               s
                                                                               tl))
                                                                     , [] ])))
                                                          (unMapData
                                                             inner2Data))
                                                   , (case hd [(\l r -> r)]) ]))
                                             (s s tl))
                                      , [] ])))
                           (\l l ->
                              (\s -> s s l)
                                (\s list ->
                                   case
                                     list
                                     [ (\hd ->
                                          (\k ->
                                             (\s ->
                                                case
                                                  (s s l)
                                                  [ (\tl ->
                                                       force mkCons hd (s s tl))
                                                  , (\tl -> s s tl) ])
                                               (\s xs ->
                                                  case
                                                    xs
                                                    [ (\hd ->
                                                         case
                                                           (equalsData
                                                              k
                                                              (case
                                                                 hd
                                                                 [(\l r -> l)]))
                                                           [ (\x -> s s x)
                                                           , (\ds -> True) ])
                                                    , False ]))
                                            (case hd [(\l r -> l)]))
                                     , [] ])))
                        (\k ->
                           (\s -> s s)
                             (\s xs ->
                                case
                                  xs
                                  [ (\hd ->
                                       case
                                         (equalsData k (case hd [(\l r -> l)]))
                                         [ (\x -> s s x)
                                         , (\ds ->
                                              constr 0
                                                [(case hd [(\l r -> r)])]) ])
                                  , (constr 1 []) ])))
                     (\z f xs -> case xs [f, z]))
                  (unMapData bd))))
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