(program
   1.1.0
   (case
      (constr 0 [(force tailList), (force headList), (force trace)])
      [ (\forced
          forced
          forced ->
           (\go ->
              (\`$fUnsafeFromDataCredential_$cunsafeFromBuiltinData` ->
                 (\`$fUnsafeFromDataStakingCredential_$cunsafeFromBuiltinData` ->
                    (\`$fUnsafeFromDataDCert_$cunsafeFromBuiltinData` ->
                       (\go ->
                          (\`$fUnsafeFromDataMap_$cunsafeFromBuiltinData` ->
                             (\`$fUnsafeFromDataTxOut_$cunsafeFromBuiltinData` ->
                                (\go ->
                                   (\`$fUnsafeFromDataTxId_$cunsafeFromBuiltinData` ->
                                      (\`$fUnsafeFromDataTxOutRef_$cunsafeFromBuiltinData` ->
                                         (\`$fUnsafeFromDataScriptContext_$cunsafeFromBuiltinData` ->
                                            (\go ->
                                               (\go
                                                 obsScriptCred
                                                 ctx ->
                                                  case
                                                    (case
                                                       (unConstrData ctx)
                                                       [ (\index
                                                           args ->
                                                            case
                                                              index
                                                              [ (\ds ->
                                                                   (\`$fUnsafeFromDataScriptContext_$cunsafeFromBuiltinData` ->
                                                                      constr 0
                                                                        [ (case
                                                                             (unConstrData
                                                                                (forced
                                                                                   ds))
                                                                             [ (\index
                                                                                 args ->
                                                                                  case
                                                                                    index
                                                                                    [ (\ds ->
                                                                                         (\l ->
                                                                                            (\l ->
                                                                                               (\l ->
                                                                                                  (\l ->
                                                                                                     (\l ->
                                                                                                        (\l ->
                                                                                                           (\l ->
                                                                                                              (\l ->
                                                                                                                 (\l ->
                                                                                                                    (\l ->
                                                                                                                       (\cse ->
                                                                                                                          (\cse ->
                                                                                                                             constr 0
                                                                                                                               [ (go
                                                                                                                                    (unListData
                                                                                                                                       (forced
                                                                                                                                          ds)))
                                                                                                                               , (go
                                                                                                                                    (unListData
                                                                                                                                       (forced
                                                                                                                                          l)))
                                                                                                                               , (go
                                                                                                                                    (unListData
                                                                                                                                       (forced
                                                                                                                                          l)))
                                                                                                                               , (cse
                                                                                                                                    (forced
                                                                                                                                       l))
                                                                                                                               , (cse
                                                                                                                                    (forced
                                                                                                                                       l))
                                                                                                                               , (go
                                                                                                                                    (unListData
                                                                                                                                       (forced
                                                                                                                                          l)))
                                                                                                                               , (case
                                                                                                                                    (constr 0
                                                                                                                                       [ `$fUnsafeFromDataStakingCredential_$cunsafeFromBuiltinData`
                                                                                                                                       , unIData
                                                                                                                                       , (forced
                                                                                                                                            l) ])
                                                                                                                                    [ `$fUnsafeFromDataMap_$cunsafeFromBuiltinData` ])
                                                                                                                               , (case
                                                                                                                                    (unConstrData
                                                                                                                                       (forced
                                                                                                                                          l))
                                                                                                                                    [ (\index
                                                                                                                                        args ->
                                                                                                                                         case
                                                                                                                                           index
                                                                                                                                           [ (\ds ->
                                                                                                                                                (\`$fUnsafeFromDataExtended_$cunsafeFromBuiltinData` ->
                                                                                                                                                   (\`$fUnsafeFromDataBool_$cunsafeFromBuiltinData` ->
                                                                                                                                                      constr 0
                                                                                                                                                        [ (case
                                                                                                                                                             (unConstrData
                                                                                                                                                                (forced
                                                                                                                                                                   ds))
                                                                                                                                                             [ (\index
                                                                                                                                                                 args ->
                                                                                                                                                                  case
                                                                                                                                                                    index
                                                                                                                                                                    [ (\ds ->
                                                                                                                                                                         constr 0
                                                                                                                                                                           [ (`$fUnsafeFromDataExtended_$cunsafeFromBuiltinData`
                                                                                                                                                                                unIData
                                                                                                                                                                                (forced
                                                                                                                                                                                   ds))
                                                                                                                                                                           , (`$fUnsafeFromDataBool_$cunsafeFromBuiltinData`
                                                                                                                                                                                (forced
                                                                                                                                                                                   (forced
                                                                                                                                                                                      ds))) ]) ]
                                                                                                                                                                    args) ])
                                                                                                                                                        , (case
                                                                                                                                                             (unConstrData
                                                                                                                                                                (forced
                                                                                                                                                                   (forced
                                                                                                                                                                      ds)))
                                                                                                                                                             [ (\index
                                                                                                                                                                 args ->
                                                                                                                                                                  case
                                                                                                                                                                    index
                                                                                                                                                                    [ (\ds ->
                                                                                                                                                                         constr 0
                                                                                                                                                                           [ (`$fUnsafeFromDataExtended_$cunsafeFromBuiltinData`
                                                                                                                                                                                unIData
                                                                                                                                                                                (forced
                                                                                                                                                                                   ds))
                                                                                                                                                                           , (`$fUnsafeFromDataBool_$cunsafeFromBuiltinData`
                                                                                                                                                                                (forced
                                                                                                                                                                                   (forced
                                                                                                                                                                                      ds))) ]) ]
                                                                                                                                                                    args) ]) ])
                                                                                                                                                     (\d ->
                                                                                                                                                        case
                                                                                                                                                          (unConstrData
                                                                                                                                                             d)
                                                                                                                                                          [ (\index
                                                                                                                                                              args ->
                                                                                                                                                               case
                                                                                                                                                                 index
                                                                                                                                                                 [ (\ds ->
                                                                                                                                                                      False)
                                                                                                                                                                 , (\ds ->
                                                                                                                                                                      True) ]
                                                                                                                                                                 args) ]))
                                                                                                                                                  (\`$dUnsafeFromData`
                                                                                                                                                    d ->
                                                                                                                                                     case
                                                                                                                                                       (unConstrData
                                                                                                                                                          d)
                                                                                                                                                       [ (\index
                                                                                                                                                           args ->
                                                                                                                                                            case
                                                                                                                                                              index
                                                                                                                                                              [ (\ds ->
                                                                                                                                                                   constr 1
                                                                                                                                                                     [  ])
                                                                                                                                                              , (\ds ->
                                                                                                                                                                   constr 0
                                                                                                                                                                     [ (`$dUnsafeFromData`
                                                                                                                                                                          (forced
                                                                                                                                                                             ds)) ])
                                                                                                                                                              , (\ds ->
                                                                                                                                                                   constr 2
                                                                                                                                                                     [  ]) ]
                                                                                                                                                              args) ])) ]
                                                                                                                                           args) ])
                                                                                                                               , (go
                                                                                                                                    (unListData
                                                                                                                                       (forced
                                                                                                                                          l)))
                                                                                                                               , (case
                                                                                                                                    (constr 0
                                                                                                                                       [ `$fUnsafeFromDataScriptContext_$cunsafeFromBuiltinData`
                                                                                                                                       , (\d ->
                                                                                                                                            d)
                                                                                                                                       , (forced
                                                                                                                                            l) ])
                                                                                                                                    [ `$fUnsafeFromDataMap_$cunsafeFromBuiltinData` ])
                                                                                                                               , (cse
                                                                                                                                    (\d ->
                                                                                                                                       d)
                                                                                                                                    (forced
                                                                                                                                       l))
                                                                                                                               , (`$fUnsafeFromDataTxId_$cunsafeFromBuiltinData`
                                                                                                                                    (forced
                                                                                                                                       (forced
                                                                                                                                          l))) ])
                                                                                                                            (cse
                                                                                                                               (cse
                                                                                                                                  unIData)))
                                                                                                                         (`$fUnsafeFromDataMap_$cunsafeFromBuiltinData`
                                                                                                                            unBData))
                                                                                                                      (forced
                                                                                                                         l))
                                                                                                                   (forced
                                                                                                                      l))
                                                                                                                (forced
                                                                                                                   l))
                                                                                                             (forced
                                                                                                                l))
                                                                                                          (forced
                                                                                                             l))
                                                                                                       (forced
                                                                                                          l))
                                                                                                    (forced
                                                                                                       l))
                                                                                                 (forced
                                                                                                    l))
                                                                                              (forced
                                                                                                 l))
                                                                                           (forced
                                                                                              ds)) ]
                                                                                    args) ])
                                                                        , (`$fUnsafeFromDataScriptContext_$cunsafeFromBuiltinData`
                                                                             (forced
                                                                                (forced
                                                                                   ds))) ])
                                                                     (\d ->
                                                                        case
                                                                          (unConstrData
                                                                             d)
                                                                          [ (\index
                                                                              args ->
                                                                               case
                                                                                 index
                                                                                 [ (\ds ->
                                                                                      constr 1
                                                                                        [ (unBData
                                                                                             (forced
                                                                                                ds)) ])
                                                                                 , (\ds ->
                                                                                      constr 3
                                                                                        [ (`$fUnsafeFromDataTxOutRef_$cunsafeFromBuiltinData`
                                                                                             (forced
                                                                                                ds)) ])
                                                                                 , (\ds ->
                                                                                      constr 2
                                                                                        [ (`$fUnsafeFromDataStakingCredential_$cunsafeFromBuiltinData`
                                                                                             (forced
                                                                                                ds)) ])
                                                                                 , (\ds ->
                                                                                      constr 0
                                                                                        [ (`$fUnsafeFromDataDCert_$cunsafeFromBuiltinData`
                                                                                             (forced
                                                                                                ds)) ]) ]
                                                                                 args) ])) ]
                                                              args) ])
                                                    [ (\ds
                                                        ds ->
                                                         case
                                                           ds
                                                           [ (\ds
                                                               ds
                                                               ds
                                                               ds
                                                               ds
                                                               ds
                                                               ds
                                                               ds
                                                               ds
                                                               ds
                                                               ds
                                                               ds ->
                                                                (\`$j` ->
                                                                   case
                                                                     ds
                                                                     [ ((\x ->
                                                                           case
                                                                             error
                                                                             [ (\a
                                                                                 ds ->
                                                                                  `$j`
                                                                                    a
                                                                                    ds) ])
                                                                          (forced
                                                                             "PT8"
                                                                             (constr 0
                                                                                [  ])))
                                                                     , (\x
                                                                         ds ->
                                                                          case
                                                                            x
                                                                            [ (\a
                                                                                ds ->
                                                                                 `$j`
                                                                                   a
                                                                                   ds) ]) ])
                                                                  (\a
                                                                    ds ->
                                                                     (\`$j` ->
                                                                        case
                                                                          ds
                                                                          [ (`$j`
                                                                               ((\x ->
                                                                                   error)
                                                                                  (forced
                                                                                     "PT9"
                                                                                     (constr 0
                                                                                        [  ]))))
                                                                          , (\ds
                                                                              as ->
                                                                               `$j`
                                                                                 as) ])
                                                                       (\rest ->
                                                                          (\`$j` ->
                                                                             case
                                                                               rest
                                                                               [ ((\x ->
                                                                                     case
                                                                                       error
                                                                                       [ (\a
                                                                                           ds ->
                                                                                            `$j`
                                                                                              a
                                                                                              ds) ])
                                                                                    (forced
                                                                                       "PT8"
                                                                                       (constr 0
                                                                                          [  ])))
                                                                               , (\x
                                                                                   ds ->
                                                                                    case
                                                                                      x
                                                                                      [ (\a
                                                                                          ds ->
                                                                                           `$j`
                                                                                             a
                                                                                             ds) ]) ])
                                                                            (\a
                                                                              ds ->
                                                                               (\obsScriptCred' ->
                                                                                  (\go ->
                                                                                     (\`$j` ->
                                                                                        case
                                                                                          obsScriptCred'
                                                                                          [ (\l1l ->
                                                                                               case
                                                                                                 a
                                                                                                 [ (\r1r ->
                                                                                                      case
                                                                                                        l1l
                                                                                                        [ (\l1l ->
                                                                                                             case
                                                                                                               r1r
                                                                                                               [ (\r1r ->
                                                                                                                    case
                                                                                                                      (equalsByteString
                                                                                                                         l1l
                                                                                                                         r1r)
                                                                                                                      [ (force
                                                                                                                           `$j`)
                                                                                                                      , (constr 0
                                                                                                                           [  ]) ])
                                                                                                               , (\ipv ->
                                                                                                                    force
                                                                                                                      `$j`) ])
                                                                                                        , (\l1l ->
                                                                                                             case
                                                                                                               r1r
                                                                                                               [ (\ipv ->
                                                                                                                    force
                                                                                                                      `$j`)
                                                                                                               , (\r1r ->
                                                                                                                    case
                                                                                                                      (equalsByteString
                                                                                                                         l1l
                                                                                                                         r1r)
                                                                                                                      [ (force
                                                                                                                           `$j`)
                                                                                                                      , (constr 0
                                                                                                                           [  ]) ]) ]) ])
                                                                                                 , (\ipv
                                                                                                     ipv
                                                                                                     ipv ->
                                                                                                      force
                                                                                                        `$j`) ])
                                                                                          , (\l1l
                                                                                              l2l
                                                                                              l3l ->
                                                                                               case
                                                                                                 a
                                                                                                 [ (\ipv ->
                                                                                                      force
                                                                                                        `$j`)
                                                                                                 , (\r1r
                                                                                                     r2r
                                                                                                     r3r ->
                                                                                                      case
                                                                                                        (case
                                                                                                           (equalsInteger
                                                                                                              l1l
                                                                                                              r1r)
                                                                                                           [ False
                                                                                                           , (case
                                                                                                                (equalsInteger
                                                                                                                   l2l
                                                                                                                   r2r)
                                                                                                                [ False
                                                                                                                , (equalsInteger
                                                                                                                     l3l
                                                                                                                     r3r) ]) ])
                                                                                                        [ (force
                                                                                                             `$j`)
                                                                                                        , (constr 0
                                                                                                             [  ]) ]) ]) ])
                                                                                       (delay
                                                                                          (case
                                                                                             obsScriptCred'
                                                                                             [ (\l1l ->
                                                                                                  case
                                                                                                    a
                                                                                                    [ (\r1r ->
                                                                                                         case
                                                                                                           l1l
                                                                                                           [ (\l1l ->
                                                                                                                case
                                                                                                                  r1r
                                                                                                                  [ (\r1r ->
                                                                                                                       case
                                                                                                                         (equalsByteString
                                                                                                                            l1l
                                                                                                                            r1r)
                                                                                                                         [ (go
                                                                                                                              ds)
                                                                                                                         , (constr 0
                                                                                                                              [  ]) ])
                                                                                                                  , (\ipv ->
                                                                                                                       go
                                                                                                                         ds) ])
                                                                                                           , (\l1l ->
                                                                                                                case
                                                                                                                  r1r
                                                                                                                  [ (\ipv ->
                                                                                                                       go
                                                                                                                         ds)
                                                                                                                  , (\r1r ->
                                                                                                                       case
                                                                                                                         (equalsByteString
                                                                                                                            l1l
                                                                                                                            r1r)
                                                                                                                         [ (go
                                                                                                                              ds)
                                                                                                                         , (constr 0
                                                                                                                              [  ]) ]) ]) ])
                                                                                                    , (\ipv
                                                                                                        ipv
                                                                                                        ipv ->
                                                                                                         go
                                                                                                           ds) ])
                                                                                             , (\l1l
                                                                                                 l2l
                                                                                                 l3l ->
                                                                                                  case
                                                                                                    a
                                                                                                    [ (\ipv ->
                                                                                                         go
                                                                                                           ds)
                                                                                                    , (\r1r
                                                                                                        r2r
                                                                                                        r3r ->
                                                                                                         case
                                                                                                           (case
                                                                                                              (equalsInteger
                                                                                                                 l1l
                                                                                                                 r1r)
                                                                                                              [ False
                                                                                                              , (case
                                                                                                                   (equalsInteger
                                                                                                                      l2l
                                                                                                                      r2r)
                                                                                                                   [ False
                                                                                                                   , (equalsInteger
                                                                                                                        l3l
                                                                                                                        r3r) ]) ])
                                                                                                           [ (go
                                                                                                                ds)
                                                                                                           , (constr 0
                                                                                                                [  ]) ]) ]) ])))
                                                                                    ((\s ->
                                                                                        s
                                                                                          s)
                                                                                       (\s
                                                                                         ds ->
                                                                                          case
                                                                                            ds
                                                                                            [ ((\x ->
                                                                                                  error)
                                                                                                 (forced
                                                                                                    "not found"
                                                                                                    (constr 0
                                                                                                       [  ])))
                                                                                            , (\ds
                                                                                                xs' ->
                                                                                                 case
                                                                                                   ds
                                                                                                   [ (\c'
                                                                                                       i ->
                                                                                                        case
                                                                                                          (case
                                                                                                             c'
                                                                                                             [ (\l1l ->
                                                                                                                  case
                                                                                                                    obsScriptCred'
                                                                                                                    [ (\r1r ->
                                                                                                                         case
                                                                                                                           l1l
                                                                                                                           [ (\l1l ->
                                                                                                                                case
                                                                                                                                  r1r
                                                                                                                                  [ (\r1r ->
                                                                                                                                       equalsByteString
                                                                                                                                         l1l
                                                                                                                                         r1r)
                                                                                                                                  , (\ipv ->
                                                                                                                                       False) ])
                                                                                                                           , (\l1l ->
                                                                                                                                case
                                                                                                                                  r1r
                                                                                                                                  [ (\ipv ->
                                                                                                                                       False)
                                                                                                                                  , (\r1r ->
                                                                                                                                       equalsByteString
                                                                                                                                         l1l
                                                                                                                                         r1r) ]) ])
                                                                                                                    , (\ipv
                                                                                                                        ipv
                                                                                                                        ipv ->
                                                                                                                         False) ])
                                                                                                             , (\l1l
                                                                                                                 l2l
                                                                                                                 l3l ->
                                                                                                                  case
                                                                                                                    obsScriptCred'
                                                                                                                    [ (\ipv ->
                                                                                                                         False)
                                                                                                                    , (\r1r
                                                                                                                        r2r
                                                                                                                        r3r ->
                                                                                                                         case
                                                                                                                           (equalsInteger
                                                                                                                              l1l
                                                                                                                              r1r)
                                                                                                                           [ False
                                                                                                                           , (case
                                                                                                                                (equalsInteger
                                                                                                                                   l2l
                                                                                                                                   r2r)
                                                                                                                                [ False
                                                                                                                                , (equalsInteger
                                                                                                                                     l3l
                                                                                                                                     r3r) ]) ]) ]) ])
                                                                                                          [ (s
                                                                                                               s
                                                                                                               xs')
                                                                                                          , (constr 0
                                                                                                               [  ]) ]) ]) ])))
                                                                                 (`$fUnsafeFromDataStakingCredential_$cunsafeFromBuiltinData`
                                                                                    obsScriptCred))))) ]) ])
                                                 ((\s ->
                                                     s s)
                                                    (\s
                                                      xs ->
                                                       case
                                                         xs
                                                         [ (\x
                                                             xs ->
                                                              constr 1
                                                                [ (`$fUnsafeFromDataScriptContext_$cunsafeFromBuiltinData`
                                                                     x)
                                                                , (s s xs) ])
                                                         , (constr 0 []) ])))
                                              ((\s ->
                                                  s s)
                                                 (\s
                                                   xs ->
                                                    case
                                                      xs
                                                      [ (\x
                                                          xs ->
                                                           constr 1
                                                             [ (`$fUnsafeFromDataScriptContext_$cunsafeFromBuiltinData`
                                                                  x)
                                                             , (s s xs) ])
                                                      , (constr 0 []) ])))
                                           (\d ->
                                              case
                                                (unConstrData d)
                                                [ (\index
                                                    args ->
                                                     case
                                                       index
                                                       [ (\ds ->
                                                            constr 0
                                                              [ (`$fUnsafeFromDataTxOutRef_$cunsafeFromBuiltinData`
                                                                   (forced ds))
                                                              , (`$fUnsafeFromDataTxOut_$cunsafeFromBuiltinData`
                                                                   (forced
                                                                      (forced
                                                                         ds))) ]) ]
                                                       args) ]))
                                        (\d ->
                                           case
                                             (unConstrData d)
                                             [ (\index
                                                 args ->
                                                  case
                                                    index
                                                    [ (\ds ->
                                                         constr 0
                                                           [ (`$fUnsafeFromDataTxId_$cunsafeFromBuiltinData`
                                                                (forced ds))
                                                           , (unIData
                                                                (forced
                                                                   (forced
                                                                      ds))) ]) ]
                                                    args) ]))
                                     (\d ->
                                        case
                                          (unConstrData d)
                                          [ (\index args ->
                                               case
                                                 index
                                                 [(\ds -> unBData (forced ds))]
                                                 args) ]))
                                  ((\s ->
                                      s s)
                                     (\s
                                       xs ->
                                        case
                                          xs
                                          [ (\x
                                              xs ->
                                               constr 1
                                                 [ (`$fUnsafeFromDataTxOut_$cunsafeFromBuiltinData`
                                                      x)
                                                 , (s s xs) ])
                                          , (constr 0 []) ])))
                               (\eta ->
                                  case
                                    (unConstrData eta)
                                    [ (\index
                                        args ->
                                         case
                                           index
                                           [ (\ds ->
                                                (\l ->
                                                   (\l ->
                                                      (\`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData` ->
                                                         constr 0
                                                           [ (case
                                                                (unConstrData
                                                                   (forced ds))
                                                                [ (\index
                                                                    args ->
                                                                     case
                                                                       index
                                                                       [ (\ds ->
                                                                            constr 0
                                                                              [ (`$fUnsafeFromDataCredential_$cunsafeFromBuiltinData`
                                                                                   (forced
                                                                                      ds))
                                                                              , (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                                                                                   `$fUnsafeFromDataStakingCredential_$cunsafeFromBuiltinData`
                                                                                   (forced
                                                                                      (forced
                                                                                         ds))) ]) ]
                                                                       args) ])
                                                           , ((\cse ->
                                                                 cse
                                                                   (cse unIData)
                                                                   (forced l))
                                                                (`$fUnsafeFromDataMap_$cunsafeFromBuiltinData`
                                                                   unBData))
                                                           , (case
                                                                (unConstrData
                                                                   (forced l))
                                                                [ (\index
                                                                    args ->
                                                                     case
                                                                       index
                                                                       [ (\ds ->
                                                                            constr 0
                                                                              [  ])
                                                                       , (\ds ->
                                                                            constr 2
                                                                              [ (unBData
                                                                                   (forced
                                                                                      ds)) ])
                                                                       , (\ds ->
                                                                            constr 1
                                                                              [ (forced
                                                                                   ds) ]) ]
                                                                       args) ])
                                                           , (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                                                                unBData
                                                                (forced
                                                                   (forced
                                                                      l))) ])
                                                        (\`$dUnsafeFromData`
                                                          d ->
                                                           case
                                                             (unConstrData d)
                                                             [ (\index
                                                                 args ->
                                                                  case
                                                                    index
                                                                    [ (\ds ->
                                                                         constr 0
                                                                           [ (`$dUnsafeFromData`
                                                                                (forced
                                                                                   ds)) ])
                                                                    , (\ds ->
                                                                         constr 1
                                                                           []) ]
                                                                    args) ]))
                                                     (forced l))
                                                  (forced ds)) ]
                                           args) ]))
                            (\`$dUnsafeFromData` `$dUnsafeFromData` ->
                               (\go d -> go (unMapData d))
                                 ((\s -> s s)
                                    (\s xs ->
                                       case
                                         xs
                                         [ (\tup tups ->
                                              constr 1
                                                [ (constr 0
                                                     [ (`$dUnsafeFromData`
                                                          (case
                                                             tup
                                                             [(\l r -> l)]))
                                                     , (`$dUnsafeFromData`
                                                          (case
                                                             tup
                                                             [(\l r -> r)])) ])
                                                , (s s tups) ])
                                         , (constr 0 []) ]))))
                         ((\s ->
                             s s)
                            (\s
                              xs ->
                               case
                                 xs
                                 [ (\x
                                     xs ->
                                      constr 1
                                        [ (`$fUnsafeFromDataDCert_$cunsafeFromBuiltinData`
                                             x)
                                        , (s s xs) ])
                                 , (constr 0 []) ])))
                      (\d ->
                         case
                           (unConstrData d)
                           [ (\index
                               args ->
                                case
                                  index
                                  [ (\ds ->
                                       constr 2
                                         [ (`$fUnsafeFromDataStakingCredential_$cunsafeFromBuiltinData`
                                              (forced ds)) ])
                                  , (\ds ->
                                       constr 0
                                         [ (`$fUnsafeFromDataStakingCredential_$cunsafeFromBuiltinData`
                                              (forced ds)) ])
                                  , (\ds ->
                                       constr 1
                                         [ (`$fUnsafeFromDataStakingCredential_$cunsafeFromBuiltinData`
                                              (forced ds))
                                         , (unBData (forced (forced ds))) ])
                                  , (\ds ->
                                       constr 5
                                         [ (unBData (forced ds))
                                         , (unBData (forced (forced ds))) ])
                                  , (\ds ->
                                       constr 6
                                         [ (unBData (forced ds))
                                         , (unIData (forced (forced ds))) ])
                                  , (\ds -> constr 3 [])
                                  , (\ds -> constr 4 []) ]
                                  args) ]))
                   (\d ->
                      case
                        (unConstrData d)
                        [ (\index
                            args ->
                             case
                               index
                               [ (\ds ->
                                    constr 0
                                      [ (`$fUnsafeFromDataCredential_$cunsafeFromBuiltinData`
                                           (forced ds)) ])
                               , (\ds ->
                                    (\l ->
                                       constr 1
                                         [ (unIData (forced ds))
                                         , (unIData (forced l))
                                         , (unIData (forced (forced l))) ])
                                      (forced ds)) ]
                               args) ]))
                (\d ->
                   case
                     (unConstrData d)
                     [ (\index args ->
                          case
                            index
                            [ (\ds -> constr 0 [(unBData (forced ds))])
                            , (\ds -> constr 1 [(unBData (forced ds))]) ]
                            args) ]))
             ((\s -> s s)
                (\s xs ->
                   case
                     xs
                     [ (\x xs -> constr 1 [(unBData x), (s s xs)])
                     , (constr 0 []) ]))) ]))