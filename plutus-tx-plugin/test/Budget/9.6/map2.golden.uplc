(program
   1.1.0
   ((\go ->
       (\go ->
          (\goList
            n ->
             (\unsafeFromSOPList ->
                (\nt ->
                   (\go ->
                      (\nt ->
                         go
                           ((\rs' ->
                               (\ls' -> go rs' ls') (go nt))
                              ((\s ->
                                  s s)
                                 (\s
                                   xs ->
                                    case
                                      xs
                                      [ (\hd
                                          tl ->
                                           (\tl' ->
                                              case
                                                ((\k ->
                                                    (\s ->
                                                       s s)
                                                      (\s
                                                        xs ->
                                                         case
                                                           xs
                                                           [ (\hd ->
                                                                case
                                                                  (equalsData
                                                                     k
                                                                     (case
                                                                        hd
                                                                        [ (\l
                                                                            r ->
                                                                             l) ]))
                                                                  [ (\x ->
                                                                       s s x)
                                                                  , (\ds ->
                                                                       True) ])
                                                           , False ])
                                                      nt)
                                                   (case hd [(\l r -> l)]))
                                                [(force mkCons hd tl'), tl'])
                                             (s s tl))
                                      , [] ])
                                 nt)))
                        (case
                           (constr 0
                              [ (\i -> iData i)
                              , (\i -> iData i)
                              , (constr 1
                                   [ (constr 0 [(addInteger 1 n), 1])
                                   , (constr 1
                                        [ (constr 0 [(addInteger 2 n), 2])
                                        , (constr 1
                                             [ (constr 0 [(addInteger 3 n), 3])
                                             , (constr 1
                                                  [ (constr 0
                                                       [(addInteger 4 n), 4])
                                                  , (constr 1
                                                       [ (constr 0
                                                            [ (addInteger 5 n)
                                                            , 5 ])
                                                       , (constr 0
                                                            [  ]) ]) ]) ]) ]) ]) ])
                           [unsafeFromSOPList]))
                     ((\s ->
                         s s)
                        (\s
                          xs ->
                           case
                             xs
                             [ (\hd
                                 tl ->
                                  (\v' ->
                                     (\k' ->
                                        case
                                          ((\s ->
                                              s s)
                                             (\s
                                               xs ->
                                                case
                                                  xs
                                                  [ (\hd ->
                                                       case
                                                         (equalsData
                                                            k'
                                                            (case
                                                               hd
                                                               [(\l r -> l)]))
                                                         [ (\x -> s s x)
                                                         , (\ds ->
                                                              constr 0
                                                                [ (case
                                                                     hd
                                                                     [ (\l
                                                                         r ->
                                                                          r) ]) ]) ])
                                                  , (constr 1 []) ])
                                             nt)
                                          [ (\r ->
                                               force mkCons
                                                 (mkPairData
                                                    k'
                                                    (iData
                                                       (addInteger
                                                          (unIData v')
                                                          (unIData r))))
                                                 (s s tl))
                                          , (force mkCons
                                               (mkPairData k' v')
                                               (s s tl)) ])
                                       (case hd [(\l r -> l)]))
                                    (case hd [(\l r -> r)]))
                             , [] ])))
                  (case
                     (constr 0
                        [ (\i -> iData i)
                        , (\i -> iData i)
                        , (constr 1
                             [ (constr 0 [(addInteger 3 n), 33])
                             , (constr 1
                                  [ (constr 0 [(addInteger 4 n), 44])
                                  , (constr 1
                                       [ (constr 0 [(addInteger 6 n), 66])
                                       , (constr 1
                                            [ (constr 0 [(addInteger 7 n), 77])
                                            , (constr 0 []) ]) ]) ]) ]) ])
                     [unsafeFromSOPList]))
               (\`$dToData` `$dToData` ->
                  (\go eta -> goList (go eta))
                    ((\s -> s s)
                       (\s ds ->
                          case
                            ds
                            [ (constr 0 [])
                            , (\x xs ->
                                 constr 1
                                   [ (case
                                        x
                                        [ (\k a ->
                                             constr 0
                                               [ (`$dToData` k)
                                               , (`$dToData` a) ]) ])
                                   , (s s xs) ]) ]))))
            ((\s -> s s)
               (\s ds ->
                  case
                    ds
                    [ []
                    , (\d ds ->
                         force mkCons
                           (case d [(\d d -> mkPairData d d)])
                           (s s ds)) ])))
         ((\s -> s s)
            (\s acc xs ->
               case xs [(\hd -> (\x -> s s x) (force mkCons hd acc)), acc])))
      ((\s -> s s)
         (\s xs ->
            case
              xs
              [ (\hd tl ->
                   constr 1
                     [ (constr 0
                          [ (unIData (case hd [(\l r -> l)]))
                          , (unIData (case hd [(\l r -> r)])) ])
                     , (s s tl) ])
              , (constr 0 []) ]))))