(program
   1.1.0
   ((\fix1
      scriptContextData ->
       force
         (case
            (force trace
               "Parsing ScriptContext..."
               (constr 0 [scriptContextData]))
            [ ((\vestingPeriodEnd ->
                  (\find ->
                     (\`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData` ->
                        (\`$mTxInfo` ->
                           (\txSignedBy ->
                              (\txOutValue ->
                                 (\`$mTxOut` ->
                                    (\txOutDatum ->
                                       (\txOutAddress ->
                                          (\txInfoValidRange ->
                                             (\txInInfoResolved ->
                                                (\totalInstallments ->
                                                   (\`$mScriptContext` ->
                                                      (\scriptContextTxInfo ->
                                                         (\scriptContextScriptInfo ->
                                                            (\traceError ->
                                                               (\getLowerInclusiveTimeRange ->
                                                                  (\addressCredential ->
                                                                     (\`$bScriptCredential` ->
                                                                        (\`$mScriptCredential` ->
                                                                           (\beneficiary ->
                                                                              (\assetClassValueOf ->
                                                                                 (\`$fUnsafeFromDataBuiltinData_$cunsafeFromBuiltinData` ->
                                                                                    (\`$mSpendingScript` ->
                                                                                       (\`$bPubKeyCredential` ->
                                                                                          (\`$mPubKeyCredential` ->
                                                                                             (\txOutRefIdx ->
                                                                                                (\txOutRefId ->
                                                                                                   (\`$bOutputDatumHash` ->
                                                                                                      (\`$bOutputDatum` ->
                                                                                                         (\`$bNoOutputDatum` ->
                                                                                                            (\`$mStakingPtr` ->
                                                                                                               (\`$fEqCredential_$c==` ->
                                                                                                                  (\divCeil
                                                                                                                    ctx ->
                                                                                                                     delay
                                                                                                                       (case
                                                                                                                          ((\context ->
                                                                                                                              force
                                                                                                                                trace
                                                                                                                                "Validation completed"
                                                                                                                                (case
                                                                                                                                   (case
                                                                                                                                      ((\d ->
                                                                                                                                          force
                                                                                                                                            chooseData
                                                                                                                                            d
                                                                                                                                            (\ds ->
                                                                                                                                               case
                                                                                                                                                 (unConstrData
                                                                                                                                                    d)
                                                                                                                                                 [ (\l
                                                                                                                                                     r ->
                                                                                                                                                      case
                                                                                                                                                        (equalsInteger
                                                                                                                                                           0
                                                                                                                                                           l)
                                                                                                                                                        [ (case
                                                                                                                                                             (equalsInteger
                                                                                                                                                                1
                                                                                                                                                                l)
                                                                                                                                                             [ (constr 1
                                                                                                                                                                  [  ])
                                                                                                                                                             , (constr 0
                                                                                                                                                                  [ (constr 0
                                                                                                                                                                       [  ]) ]) ])
                                                                                                                                                        , (constr 0
                                                                                                                                                             [ (constr 1
                                                                                                                                                                  [  ]) ]) ]) ])
                                                                                                                                            (\ds ->
                                                                                                                                               constr 1
                                                                                                                                                 [  ])
                                                                                                                                            (\ds ->
                                                                                                                                               constr 1
                                                                                                                                                 [  ])
                                                                                                                                            (\ds ->
                                                                                                                                               constr 1
                                                                                                                                                 [  ])
                                                                                                                                            (\ds ->
                                                                                                                                               constr 1
                                                                                                                                                 [  ])
                                                                                                                                            (constr 0
                                                                                                                                               [  ]))
                                                                                                                                         (`$mScriptContext`
                                                                                                                                            context
                                                                                                                                            (\ds
                                                                                                                                              ds
                                                                                                                                              ds ->
                                                                                                                                               ds)
                                                                                                                                            (\void ->
                                                                                                                                               error)))
                                                                                                                                      [ (\r ->
                                                                                                                                           force
                                                                                                                                             trace
                                                                                                                                             "Parsed Redeemer"
                                                                                                                                             r)
                                                                                                                                      , ((\x ->
                                                                                                                                            error)
                                                                                                                                           (force
                                                                                                                                              trace
                                                                                                                                              "Failed to parse Redeemer"
                                                                                                                                              (constr 0
                                                                                                                                                 [  ]))) ])
                                                                                                                                   [ ((\ctx ->
                                                                                                                                         case
                                                                                                                                           (`$mSpendingScript`
                                                                                                                                              (scriptContextScriptInfo
                                                                                                                                                 ctx)
                                                                                                                                              (\_ownRef
                                                                                                                                                ds ->
                                                                                                                                                 case
                                                                                                                                                   ds
                                                                                                                                                   [ (\ds ->
                                                                                                                                                        constr 0
                                                                                                                                                          [ _ownRef
                                                                                                                                                          , ds ])
                                                                                                                                                   , ((\defaultBody ->
                                                                                                                                                         case
                                                                                                                                                           error
                                                                                                                                                           [ defaultBody ])
                                                                                                                                                        error) ])
                                                                                                                                              (\void ->
                                                                                                                                                 (\defaultBody ->
                                                                                                                                                    case
                                                                                                                                                      error
                                                                                                                                                      [ defaultBody ])
                                                                                                                                                   error))
                                                                                                                                           [ (\ipv
                                                                                                                                               ipv ->
                                                                                                                                                (\vestingDatum ->
                                                                                                                                                   case
                                                                                                                                                     (`$mPubKeyCredential`
                                                                                                                                                        (addressCredential
                                                                                                                                                           (beneficiary
                                                                                                                                                              vestingDatum))
                                                                                                                                                        (\beneficiaryKey ->
                                                                                                                                                           constr 0
                                                                                                                                                             [ beneficiaryKey ])
                                                                                                                                                        (\void ->
                                                                                                                                                           (\defaultBody ->
                                                                                                                                                              case
                                                                                                                                                                error
                                                                                                                                                                [ defaultBody ])
                                                                                                                                                             error))
                                                                                                                                                     [ (\ipv ->
                                                                                                                                                          (\txInfo ->
                                                                                                                                                             (\ds ->
                                                                                                                                                                case
                                                                                                                                                                  (txSignedBy
                                                                                                                                                                     txInfo
                                                                                                                                                                     ipv)
                                                                                                                                                                  [ (traceError
                                                                                                                                                                       "Missing beneficiary signature")
                                                                                                                                                                  , (case
                                                                                                                                                                       (lessThanInteger
                                                                                                                                                                          (vestingPeriodEnd
                                                                                                                                                                             vestingDatum)
                                                                                                                                                                          ds)
                                                                                                                                                                       [ (traceError
                                                                                                                                                                            "Unlock not permitted until vestingPeriodEnd time")
                                                                                                                                                                       , True ]) ])
                                                                                                                                                               (getLowerInclusiveTimeRange
                                                                                                                                                                  (txInfoValidRange
                                                                                                                                                                     txInfo)))
                                                                                                                                                            (scriptContextTxInfo
                                                                                                                                                               ctx)) ])
                                                                                                                                                  (case
                                                                                                                                                     (unConstrData
                                                                                                                                                        ipv)
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
                                                                                                                                                                                constr 0
                                                                                                                                                                                  [ (force
                                                                                                                                                                                       headList
                                                                                                                                                                                       ds)
                                                                                                                                                                                  , (case
                                                                                                                                                                                       (unConstrData
                                                                                                                                                                                          (force
                                                                                                                                                                                             headList
                                                                                                                                                                                             l))
                                                                                                                                                                                       [ (\index
                                                                                                                                                                                           args ->
                                                                                                                                                                                            case
                                                                                                                                                                                              index
                                                                                                                                                                                              [ (\ds ->
                                                                                                                                                                                                   constr 0
                                                                                                                                                                                                     [ (unBData
                                                                                                                                                                                                          (force
                                                                                                                                                                                                             headList
                                                                                                                                                                                                             ds))
                                                                                                                                                                                                     , (unBData
                                                                                                                                                                                                          (force
                                                                                                                                                                                                             headList
                                                                                                                                                                                                             (force
                                                                                                                                                                                                                tailList
                                                                                                                                                                                                                ds))) ]) ]
                                                                                                                                                                                              args) ])
                                                                                                                                                                                  , (unIData
                                                                                                                                                                                       (force
                                                                                                                                                                                          headList
                                                                                                                                                                                          l))
                                                                                                                                                                                  , (unIData
                                                                                                                                                                                       (force
                                                                                                                                                                                          headList
                                                                                                                                                                                          l))
                                                                                                                                                                                  , (unIData
                                                                                                                                                                                       (force
                                                                                                                                                                                          headList
                                                                                                                                                                                          l))
                                                                                                                                                                                  , (unIData
                                                                                                                                                                                       (force
                                                                                                                                                                                          headList
                                                                                                                                                                                          l))
                                                                                                                                                                                  , (unIData
                                                                                                                                                                                       (force
                                                                                                                                                                                          headList
                                                                                                                                                                                          (force
                                                                                                                                                                                             tailList
                                                                                                                                                                                             l))) ])
                                                                                                                                                                               (force
                                                                                                                                                                                  tailList
                                                                                                                                                                                  l))
                                                                                                                                                                            (force
                                                                                                                                                                               tailList
                                                                                                                                                                               l))
                                                                                                                                                                         (force
                                                                                                                                                                            tailList
                                                                                                                                                                            l))
                                                                                                                                                                      (force
                                                                                                                                                                         tailList
                                                                                                                                                                         l))
                                                                                                                                                                   (force
                                                                                                                                                                      tailList
                                                                                                                                                                      ds)) ]
                                                                                                                                                            args) ])) ])
                                                                                                                                        (force
                                                                                                                                           trace
                                                                                                                                           "Full unlock requested"
                                                                                                                                           context))
                                                                                                                                   , ((\ctx ->
                                                                                                                                         case
                                                                                                                                           (`$mSpendingScript`
                                                                                                                                              (scriptContextScriptInfo
                                                                                                                                                 ctx)
                                                                                                                                              (\ownRef
                                                                                                                                                ds ->
                                                                                                                                                 case
                                                                                                                                                   ds
                                                                                                                                                   [ (\ds ->
                                                                                                                                                        constr 0
                                                                                                                                                          [ ownRef
                                                                                                                                                          , ds ])
                                                                                                                                                   , ((\defaultBody ->
                                                                                                                                                         case
                                                                                                                                                           error
                                                                                                                                                           [ defaultBody ])
                                                                                                                                                        error) ])
                                                                                                                                              (\void ->
                                                                                                                                                 (\defaultBody ->
                                                                                                                                                    case
                                                                                                                                                      error
                                                                                                                                                      [ defaultBody ])
                                                                                                                                                   error))
                                                                                                                                           [ (\ipv
                                                                                                                                               ipv ->
                                                                                                                                                (\vestingDatum ->
                                                                                                                                                   (\ds ->
                                                                                                                                                      (\ds ->
                                                                                                                                                         case
                                                                                                                                                           (`$mPubKeyCredential`
                                                                                                                                                              (addressCredential
                                                                                                                                                                 (beneficiary
                                                                                                                                                                    vestingDatum))
                                                                                                                                                              (\beneficiaryHash ->
                                                                                                                                                                 constr 0
                                                                                                                                                                   [ beneficiaryHash ])
                                                                                                                                                              (\void ->
                                                                                                                                                                 (\defaultBody ->
                                                                                                                                                                    case
                                                                                                                                                                      error
                                                                                                                                                                      [ defaultBody ])
                                                                                                                                                                   error))
                                                                                                                                                           [ ((\asset
                                                                                                                                                                ipv ->
                                                                                                                                                                 (\txInfo ->
                                                                                                                                                                    (\nt ->
                                                                                                                                                                       case
                                                                                                                                                                         (case
                                                                                                                                                                            (find
                                                                                                                                                                               `$fUnsafeFromDataBuiltinData_$cunsafeFromBuiltinData`
                                                                                                                                                                               (\eta ->
                                                                                                                                                                                  (\l ->
                                                                                                                                                                                     case
                                                                                                                                                                                       (equalsByteString
                                                                                                                                                                                          (txOutRefId
                                                                                                                                                                                             l)
                                                                                                                                                                                          (txOutRefId
                                                                                                                                                                                             ipv))
                                                                                                                                                                                       [ False
                                                                                                                                                                                       , (equalsInteger
                                                                                                                                                                                            (txOutRefIdx
                                                                                                                                                                                               l)
                                                                                                                                                                                            (txOutRefIdx
                                                                                                                                                                                               ipv)) ])
                                                                                                                                                                                    (force
                                                                                                                                                                                       headList
                                                                                                                                                                                       (case
                                                                                                                                                                                          (unConstrData
                                                                                                                                                                                             eta)
                                                                                                                                                                                          [ (\l
                                                                                                                                                                                              r ->
                                                                                                                                                                                               r) ])))
                                                                                                                                                                               nt)
                                                                                                                                                                            [ (\ownVestingInput ->
                                                                                                                                                                                 constr 0
                                                                                                                                                                                   [ ownVestingInput ])
                                                                                                                                                                            , ((\defaultBody ->
                                                                                                                                                                                  case
                                                                                                                                                                                    error
                                                                                                                                                                                    [ defaultBody ])
                                                                                                                                                                                 error) ])
                                                                                                                                                                         [ (\ipv ->
                                                                                                                                                                              (\nt ->
                                                                                                                                                                                 (\nt ->
                                                                                                                                                                                    case
                                                                                                                                                                                      (`$mScriptCredential`
                                                                                                                                                                                         (addressCredential
                                                                                                                                                                                            nt)
                                                                                                                                                                                         (\scriptHash ->
                                                                                                                                                                                            constr 0
                                                                                                                                                                                              [ scriptHash ])
                                                                                                                                                                                         (\void ->
                                                                                                                                                                                            (\defaultBody ->
                                                                                                                                                                                               case
                                                                                                                                                                                                 error
                                                                                                                                                                                                 [ defaultBody ])
                                                                                                                                                                                              error))
                                                                                                                                                                                      [ (\ipv ->
                                                                                                                                                                                           (\go ->
                                                                                                                                                                                              (\ds ->
                                                                                                                                                                                                 (\ownVestingOutput ->
                                                                                                                                                                                                    (\nt ->
                                                                                                                                                                                                       (\ds ->
                                                                                                                                                                                                          (\currentTimeApproximation ->
                                                                                                                                                                                                             (\ds ->
                                                                                                                                                                                                                case
                                                                                                                                                                                                                  (txSignedBy
                                                                                                                                                                                                                     txInfo
                                                                                                                                                                                                                     ipv)
                                                                                                                                                                                                                  [ (traceError
                                                                                                                                                                                                                       "Missing beneficiary signature")
                                                                                                                                                                                                                  , (case
                                                                                                                                                                                                                       (lessThanInteger
                                                                                                                                                                                                                          (case
                                                                                                                                                                                                                             vestingDatum
                                                                                                                                                                                                                             [ (\ds
                                                                                                                                                                                                                                 ds
                                                                                                                                                                                                                                 ds
                                                                                                                                                                                                                                 ds
                                                                                                                                                                                                                                 ds
                                                                                                                                                                                                                                 ds
                                                                                                                                                                                                                                 ds ->
                                                                                                                                                                                                                                  ds) ])
                                                                                                                                                                                                                          currentTimeApproximation)
                                                                                                                                                                                                                       [ (traceError
                                                                                                                                                                                                                            "Unlock not permitted until firstUnlockPossibleAfter time")
                                                                                                                                                                                                                       , (force
                                                                                                                                                                                                                            ((\newRemainingQty ->
                                                                                                                                                                                                                                case
                                                                                                                                                                                                                                  (lessThanEqualsInteger
                                                                                                                                                                                                                                     (force
                                                                                                                                                                                                                                        newRemainingQty)
                                                                                                                                                                                                                                     0)
                                                                                                                                                                                                                                  [ (delay
                                                                                                                                                                                                                                       (case
                                                                                                                                                                                                                                          (lessThanInteger
                                                                                                                                                                                                                                             (force
                                                                                                                                                                                                                                                newRemainingQty)
                                                                                                                                                                                                                                             ds)
                                                                                                                                                                                                                                          [ (traceError
                                                                                                                                                                                                                                               "Remaining asset is not decreasing")
                                                                                                                                                                                                                                          , (case
                                                                                                                                                                                                                                               (equalsInteger
                                                                                                                                                                                                                                                  ds
                                                                                                                                                                                                                                                  (force
                                                                                                                                                                                                                                                     newRemainingQty))
                                                                                                                                                                                                                                               [ (traceError
                                                                                                                                                                                                                                                    "Mismatched remaining asset")
                                                                                                                                                                                                                                               , (case
                                                                                                                                                                                                                                                    ((\ds ->
                                                                                                                                                                                                                                                        force
                                                                                                                                                                                                                                                          ((\fail ->
                                                                                                                                                                                                                                                              case
                                                                                                                                                                                                                                                                (equalsInteger
                                                                                                                                                                                                                                                                   `$bNoOutputDatum`
                                                                                                                                                                                                                                                                   (case
                                                                                                                                                                                                                                                                      (unConstrData
                                                                                                                                                                                                                                                                         ds)
                                                                                                                                                                                                                                                                      [ (\l
                                                                                                                                                                                                                                                                          r ->
                                                                                                                                                                                                                                                                           l) ]))
                                                                                                                                                                                                                                                                [ (delay
                                                                                                                                                                                                                                                                     (fail
                                                                                                                                                                                                                                                                        ()))
                                                                                                                                                                                                                                                                , (delay
                                                                                                                                                                                                                                                                     (case
                                                                                                                                                                                                                                                                        (equalsInteger
                                                                                                                                                                                                                                                                           `$bNoOutputDatum`
                                                                                                                                                                                                                                                                           (case
                                                                                                                                                                                                                                                                              (unConstrData
                                                                                                                                                                                                                                                                                 nt)
                                                                                                                                                                                                                                                                              [ (\l
                                                                                                                                                                                                                                                                                  r ->
                                                                                                                                                                                                                                                                                   l) ]))
                                                                                                                                                                                                                                                                        [ (fail
                                                                                                                                                                                                                                                                             ())
                                                                                                                                                                                                                                                                        , True ])) ])
                                                                                                                                                                                                                                                             ((\fail
                                                                                                                                                                                                                                                                ds ->
                                                                                                                                                                                                                                                                 (\tup ->
                                                                                                                                                                                                                                                                    case
                                                                                                                                                                                                                                                                      (equalsInteger
                                                                                                                                                                                                                                                                         `$bOutputDatumHash`
                                                                                                                                                                                                                                                                         (case
                                                                                                                                                                                                                                                                            tup
                                                                                                                                                                                                                                                                            [ (\l
                                                                                                                                                                                                                                                                                r ->
                                                                                                                                                                                                                                                                                 l) ]))
                                                                                                                                                                                                                                                                      [ (fail
                                                                                                                                                                                                                                                                           ())
                                                                                                                                                                                                                                                                      , ((\tup ->
                                                                                                                                                                                                                                                                            case
                                                                                                                                                                                                                                                                              (equalsInteger
                                                                                                                                                                                                                                                                                 `$bOutputDatumHash`
                                                                                                                                                                                                                                                                                 (case
                                                                                                                                                                                                                                                                                    tup
                                                                                                                                                                                                                                                                                    [ (\l
                                                                                                                                                                                                                                                                                        r ->
                                                                                                                                                                                                                                                                                         l) ]))
                                                                                                                                                                                                                                                                              [ (fail
                                                                                                                                                                                                                                                                                   ())
                                                                                                                                                                                                                                                                              , (equalsByteString
                                                                                                                                                                                                                                                                                   (unBData
                                                                                                                                                                                                                                                                                      (force
                                                                                                                                                                                                                                                                                         headList
                                                                                                                                                                                                                                                                                         (case
                                                                                                                                                                                                                                                                                            tup
                                                                                                                                                                                                                                                                                            [ (\l
                                                                                                                                                                                                                                                                                                r ->
                                                                                                                                                                                                                                                                                                 r) ])))
                                                                                                                                                                                                                                                                                   (unBData
                                                                                                                                                                                                                                                                                      (force
                                                                                                                                                                                                                                                                                         headList
                                                                                                                                                                                                                                                                                         (case
                                                                                                                                                                                                                                                                                            tup
                                                                                                                                                                                                                                                                                            [ (\l
                                                                                                                                                                                                                                                                                                r ->
                                                                                                                                                                                                                                                                                                 r) ])))) ])
                                                                                                                                                                                                                                                                           (unConstrData
                                                                                                                                                                                                                                                                              nt)) ])
                                                                                                                                                                                                                                                                   (unConstrData
                                                                                                                                                                                                                                                                      ds))
                                                                                                                                                                                                                                                                (\ds ->
                                                                                                                                                                                                                                                                   (\tup ->
                                                                                                                                                                                                                                                                      case
                                                                                                                                                                                                                                                                        (equalsInteger
                                                                                                                                                                                                                                                                           `$bOutputDatum`
                                                                                                                                                                                                                                                                           (case
                                                                                                                                                                                                                                                                              tup
                                                                                                                                                                                                                                                                              [ (\l
                                                                                                                                                                                                                                                                                  r ->
                                                                                                                                                                                                                                                                                   l) ]))
                                                                                                                                                                                                                                                                        [ False
                                                                                                                                                                                                                                                                        , ((\tup ->
                                                                                                                                                                                                                                                                              case
                                                                                                                                                                                                                                                                                (equalsInteger
                                                                                                                                                                                                                                                                                   `$bOutputDatum`
                                                                                                                                                                                                                                                                                   (case
                                                                                                                                                                                                                                                                                      tup
                                                                                                                                                                                                                                                                                      [ (\l
                                                                                                                                                                                                                                                                                          r ->
                                                                                                                                                                                                                                                                                           l) ]))
                                                                                                                                                                                                                                                                                [ False
                                                                                                                                                                                                                                                                                , (equalsData
                                                                                                                                                                                                                                                                                     (force
                                                                                                                                                                                                                                                                                        headList
                                                                                                                                                                                                                                                                                        (case
                                                                                                                                                                                                                                                                                           tup
                                                                                                                                                                                                                                                                                           [ (\l
                                                                                                                                                                                                                                                                                               r ->
                                                                                                                                                                                                                                                                                                r) ]))
                                                                                                                                                                                                                                                                                     (force
                                                                                                                                                                                                                                                                                        headList
                                                                                                                                                                                                                                                                                        (case
                                                                                                                                                                                                                                                                                           tup
                                                                                                                                                                                                                                                                                           [ (\l
                                                                                                                                                                                                                                                                                               r ->
                                                                                                                                                                                                                                                                                                r) ]))) ])
                                                                                                                                                                                                                                                                             (unConstrData
                                                                                                                                                                                                                                                                                nt)) ])
                                                                                                                                                                                                                                                                     (unConstrData
                                                                                                                                                                                                                                                                        ds)))))
                                                                                                                                                                                                                                                       (txOutDatum
                                                                                                                                                                                                                                                          nt))
                                                                                                                                                                                                                                                    [ (traceError
                                                                                                                                                                                                                                                         "Datum Modification Prohibited")
                                                                                                                                                                                                                                                    , (case
                                                                                                                                                                                                                                                         (equalsInteger
                                                                                                                                                                                                                                                            (go
                                                                                                                                                                                                                                                               0
                                                                                                                                                                                                                                                               nt)
                                                                                                                                                                                                                                                            1)
                                                                                                                                                                                                                                                         [ (traceError
                                                                                                                                                                                                                                                              "Double satisfaction")
                                                                                                                                                                                                                                                         , True ]) ]) ]) ]))
                                                                                                                                                                                                                                  , (delay
                                                                                                                                                                                                                                       (traceError
                                                                                                                                                                                                                                          "Zero remaining assets not allowed")) ])
                                                                                                                                                                                                                               (delay
                                                                                                                                                                                                                                  (case
                                                                                                                                                                                                                                     ds
                                                                                                                                                                                                                                     [ (\newRemainingQty ->
                                                                                                                                                                                                                                          newRemainingQty) ])))) ]) ])
                                                                                                                                                                                                               (divCeil
                                                                                                                                                                                                                  (multiplyInteger
                                                                                                                                                                                                                     (divCeil
                                                                                                                                                                                                                        (subtractInteger
                                                                                                                                                                                                                           (vestingPeriodEnd
                                                                                                                                                                                                                              vestingDatum)
                                                                                                                                                                                                                           currentTimeApproximation)
                                                                                                                                                                                                                        ds)
                                                                                                                                                                                                                     (case
                                                                                                                                                                                                                        vestingDatum
                                                                                                                                                                                                                        [ (\ds
                                                                                                                                                                                                                            ds
                                                                                                                                                                                                                            ds
                                                                                                                                                                                                                            ds
                                                                                                                                                                                                                            ds
                                                                                                                                                                                                                            ds
                                                                                                                                                                                                                            ds ->
                                                                                                                                                                                                                             ds) ]))
                                                                                                                                                                                                                  (totalInstallments
                                                                                                                                                                                                                     vestingDatum)))
                                                                                                                                                                                                            (getLowerInclusiveTimeRange
                                                                                                                                                                                                               (txInfoValidRange
                                                                                                                                                                                                                  txInfo)))
                                                                                                                                                                                                         (constr 0
                                                                                                                                                                                                            [ (assetClassValueOf
                                                                                                                                                                                                                 (txOutValue
                                                                                                                                                                                                                    ownVestingOutput)
                                                                                                                                                                                                                 (force
                                                                                                                                                                                                                    asset)) ]))
                                                                                                                                                                                                      (txOutDatum
                                                                                                                                                                                                         ownVestingOutput))
                                                                                                                                                                                                   (case
                                                                                                                                                                                                      (case
                                                                                                                                                                                                         (find
                                                                                                                                                                                                            `$fUnsafeFromDataBuiltinData_$cunsafeFromBuiltinData`
                                                                                                                                                                                                            (\eta ->
                                                                                                                                                                                                               (\l ->
                                                                                                                                                                                                                  (\l ->
                                                                                                                                                                                                                     case
                                                                                                                                                                                                                       (`$fEqCredential_$c==`
                                                                                                                                                                                                                          (force
                                                                                                                                                                                                                             headList
                                                                                                                                                                                                                             l)
                                                                                                                                                                                                                          (force
                                                                                                                                                                                                                             headList
                                                                                                                                                                                                                             l))
                                                                                                                                                                                                                       [ False
                                                                                                                                                                                                                       , (case
                                                                                                                                                                                                                            (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                                                                                                                                                                                                                               `$fUnsafeFromDataBuiltinData_$cunsafeFromBuiltinData`
                                                                                                                                                                                                                               (force
                                                                                                                                                                                                                                  headList
                                                                                                                                                                                                                                  (force
                                                                                                                                                                                                                                     tailList
                                                                                                                                                                                                                                     l)))
                                                                                                                                                                                                                            [ (\l1l ->
                                                                                                                                                                                                                                 case
                                                                                                                                                                                                                                   (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                                                                                                                                                                                                                                      `$fUnsafeFromDataBuiltinData_$cunsafeFromBuiltinData`
                                                                                                                                                                                                                                      (force
                                                                                                                                                                                                                                         headList
                                                                                                                                                                                                                                         (force
                                                                                                                                                                                                                                            tailList
                                                                                                                                                                                                                                            l)))
                                                                                                                                                                                                                                   [ (\r1r ->
                                                                                                                                                                                                                                        (\tup ->
                                                                                                                                                                                                                                           force
                                                                                                                                                                                                                                             ((\fail ->
                                                                                                                                                                                                                                                 case
                                                                                                                                                                                                                                                   (equalsInteger
                                                                                                                                                                                                                                                      `$bPubKeyCredential`
                                                                                                                                                                                                                                                      (case
                                                                                                                                                                                                                                                         tup
                                                                                                                                                                                                                                                         [ (\l
                                                                                                                                                                                                                                                             r ->
                                                                                                                                                                                                                                                              l) ]))
                                                                                                                                                                                                                                                   [ (delay
                                                                                                                                                                                                                                                        (fail
                                                                                                                                                                                                                                                           ()))
                                                                                                                                                                                                                                                   , (delay
                                                                                                                                                                                                                                                        ((\tup ->
                                                                                                                                                                                                                                                            case
                                                                                                                                                                                                                                                              (equalsInteger
                                                                                                                                                                                                                                                                 `$bPubKeyCredential`
                                                                                                                                                                                                                                                                 (case
                                                                                                                                                                                                                                                                    tup
                                                                                                                                                                                                                                                                    [ (\l
                                                                                                                                                                                                                                                                        r ->
                                                                                                                                                                                                                                                                         l) ]))
                                                                                                                                                                                                                                                              [ (fail
                                                                                                                                                                                                                                                                   ())
                                                                                                                                                                                                                                                              , (`$fEqCredential_$c==`
                                                                                                                                                                                                                                                                   (force
                                                                                                                                                                                                                                                                      headList
                                                                                                                                                                                                                                                                      (case
                                                                                                                                                                                                                                                                         tup
                                                                                                                                                                                                                                                                         [ (\l
                                                                                                                                                                                                                                                                             r ->
                                                                                                                                                                                                                                                                              r) ]))
                                                                                                                                                                                                                                                                   (force
                                                                                                                                                                                                                                                                      headList
                                                                                                                                                                                                                                                                      (case
                                                                                                                                                                                                                                                                         tup
                                                                                                                                                                                                                                                                         [ (\l
                                                                                                                                                                                                                                                                             r ->
                                                                                                                                                                                                                                                                              r) ]))) ])
                                                                                                                                                                                                                                                           (unConstrData
                                                                                                                                                                                                                                                              r1r))) ])
                                                                                                                                                                                                                                                (\ds ->
                                                                                                                                                                                                                                                   `$mStakingPtr`
                                                                                                                                                                                                                                                     l1l
                                                                                                                                                                                                                                                     (\a
                                                                                                                                                                                                                                                       b
                                                                                                                                                                                                                                                       c ->
                                                                                                                                                                                                                                                        `$mStakingPtr`
                                                                                                                                                                                                                                                          r1r
                                                                                                                                                                                                                                                          (\a'
                                                                                                                                                                                                                                                            b'
                                                                                                                                                                                                                                                            c' ->
                                                                                                                                                                                                                                                             case
                                                                                                                                                                                                                                                               (equalsInteger
                                                                                                                                                                                                                                                                  a
                                                                                                                                                                                                                                                                  a')
                                                                                                                                                                                                                                                               [ False
                                                                                                                                                                                                                                                               , (case
                                                                                                                                                                                                                                                                    (equalsInteger
                                                                                                                                                                                                                                                                       b
                                                                                                                                                                                                                                                                       b')
                                                                                                                                                                                                                                                                    [ False
                                                                                                                                                                                                                                                                    , (equalsInteger
                                                                                                                                                                                                                                                                         c
                                                                                                                                                                                                                                                                         c') ]) ])
                                                                                                                                                                                                                                                          (\void ->
                                                                                                                                                                                                                                                             False))
                                                                                                                                                                                                                                                     (\void ->
                                                                                                                                                                                                                                                        False))))
                                                                                                                                                                                                                                          (unConstrData
                                                                                                                                                                                                                                             l1l))
                                                                                                                                                                                                                                   , False ])
                                                                                                                                                                                                                            , (case
                                                                                                                                                                                                                                 (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                                                                                                                                                                                                                                    `$fUnsafeFromDataBuiltinData_$cunsafeFromBuiltinData`
                                                                                                                                                                                                                                    (force
                                                                                                                                                                                                                                       headList
                                                                                                                                                                                                                                       (force
                                                                                                                                                                                                                                          tailList
                                                                                                                                                                                                                                          l)))
                                                                                                                                                                                                                                 [ (\ipv ->
                                                                                                                                                                                                                                      False)
                                                                                                                                                                                                                                 , True ]) ]) ])
                                                                                                                                                                                                                    (case
                                                                                                                                                                                                                       (unConstrData
                                                                                                                                                                                                                          nt)
                                                                                                                                                                                                                       [ (\l
                                                                                                                                                                                                                           r ->
                                                                                                                                                                                                                            r) ]))
                                                                                                                                                                                                                 (case
                                                                                                                                                                                                                    (unConstrData
                                                                                                                                                                                                                       (txOutAddress
                                                                                                                                                                                                                          eta))
                                                                                                                                                                                                                    [ (\l
                                                                                                                                                                                                                        r ->
                                                                                                                                                                                                                         r) ]))
                                                                                                                                                                                                            (`$mTxInfo`
                                                                                                                                                                                                               txInfo
                                                                                                                                                                                                               (\ds
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
                                                                                                                                                                                                                 ds
                                                                                                                                                                                                                 ds
                                                                                                                                                                                                                 ds
                                                                                                                                                                                                                 ds
                                                                                                                                                                                                                 ds ->
                                                                                                                                                                                                                  ds)
                                                                                                                                                                                                               (\void ->
                                                                                                                                                                                                                  error)))
                                                                                                                                                                                                         [ (\ownVestingOutput ->
                                                                                                                                                                                                              constr 0
                                                                                                                                                                                                                [ ownVestingOutput ])
                                                                                                                                                                                                         , ((\defaultBody ->
                                                                                                                                                                                                               case
                                                                                                                                                                                                                 error
                                                                                                                                                                                                                 [ defaultBody ])
                                                                                                                                                                                                              error) ])
                                                                                                                                                                                                      [ (\ownVestingOutput ->
                                                                                                                                                                                                           ownVestingOutput) ]))
                                                                                                                                                                                                (assetClassValueOf
                                                                                                                                                                                                   (txOutValue
                                                                                                                                                                                                      nt)
                                                                                                                                                                                                   (force
                                                                                                                                                                                                      asset)))
                                                                                                                                                                                             (fix1
                                                                                                                                                                                                (\go
                                                                                                                                                                                                  n
                                                                                                                                                                                                  ds ->
                                                                                                                                                                                                   case
                                                                                                                                                                                                     ds
                                                                                                                                                                                                     [ (\x
                                                                                                                                                                                                         eta ->
                                                                                                                                                                                                          `$mScriptCredential`
                                                                                                                                                                                                            (addressCredential
                                                                                                                                                                                                               (txOutAddress
                                                                                                                                                                                                                  (txInInfoResolved
                                                                                                                                                                                                                     x)))
                                                                                                                                                                                                            (\vh ->
                                                                                                                                                                                                               case
                                                                                                                                                                                                                 (equalsByteString
                                                                                                                                                                                                                    vh
                                                                                                                                                                                                                    ipv)
                                                                                                                                                                                                                 [ (go
                                                                                                                                                                                                                      n
                                                                                                                                                                                                                      eta)
                                                                                                                                                                                                                 , (go
                                                                                                                                                                                                                      (addInteger
                                                                                                                                                                                                                         1
                                                                                                                                                                                                                         n)
                                                                                                                                                                                                                      eta) ])
                                                                                                                                                                                                            (\void ->
                                                                                                                                                                                                               go
                                                                                                                                                                                                                 n
                                                                                                                                                                                                                 eta))
                                                                                                                                                                                                     , n ]))) ])
                                                                                                                                                                                   (txOutAddress
                                                                                                                                                                                      nt))
                                                                                                                                                                                (txInInfoResolved
                                                                                                                                                                                   ipv)) ])
                                                                                                                                                                      (`$mTxInfo`
                                                                                                                                                                         txInfo
                                                                                                                                                                         (\ds
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
                                                                                                                                                                           ds
                                                                                                                                                                           ds
                                                                                                                                                                           ds
                                                                                                                                                                           ds
                                                                                                                                                                           ds ->
                                                                                                                                                                            ds)
                                                                                                                                                                         (\void ->
                                                                                                                                                                            error)))
                                                                                                                                                                   (scriptContextTxInfo
                                                                                                                                                                      ctx))
                                                                                                                                                                (delay
                                                                                                                                                                   (case
                                                                                                                                                                      ds
                                                                                                                                                                      [ (\asset ->
                                                                                                                                                                           asset) ]))) ])
                                                                                                                                                        (divCeil
                                                                                                                                                           (subtractInteger
                                                                                                                                                              (vestingPeriodEnd
                                                                                                                                                                 vestingDatum)
                                                                                                                                                              (case
                                                                                                                                                                 vestingDatum
                                                                                                                                                                 [ (\ds
                                                                                                                                                                     ds
                                                                                                                                                                     ds
                                                                                                                                                                     ds
                                                                                                                                                                     ds
                                                                                                                                                                     ds
                                                                                                                                                                     ds ->
                                                                                                                                                                      ds) ]))
                                                                                                                                                           (totalInstallments
                                                                                                                                                              vestingDatum)))
                                                                                                                                                     (constr 0
                                                                                                                                                        [ (case
                                                                                                                                                             vestingDatum
                                                                                                                                                             [ (\ds
                                                                                                                                                                 ds
                                                                                                                                                                 ds
                                                                                                                                                                 ds
                                                                                                                                                                 ds
                                                                                                                                                                 ds
                                                                                                                                                                 ds ->
                                                                                                                                                                  ds) ]) ]))
                                                                                                                                                  (case
                                                                                                                                                     (unConstrData
                                                                                                                                                        ipv)
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
                                                                                                                                                                                constr 0
                                                                                                                                                                                  [ (force
                                                                                                                                                                                       headList
                                                                                                                                                                                       ds)
                                                                                                                                                                                  , (case
                                                                                                                                                                                       (unConstrData
                                                                                                                                                                                          (force
                                                                                                                                                                                             headList
                                                                                                                                                                                             l))
                                                                                                                                                                                       [ (\index
                                                                                                                                                                                           args ->
                                                                                                                                                                                            case
                                                                                                                                                                                              index
                                                                                                                                                                                              [ (\ds ->
                                                                                                                                                                                                   constr 0
                                                                                                                                                                                                     [ (unBData
                                                                                                                                                                                                          (force
                                                                                                                                                                                                             headList
                                                                                                                                                                                                             ds))
                                                                                                                                                                                                     , (unBData
                                                                                                                                                                                                          (force
                                                                                                                                                                                                             headList
                                                                                                                                                                                                             (force
                                                                                                                                                                                                                tailList
                                                                                                                                                                                                                ds))) ]) ]
                                                                                                                                                                                              args) ])
                                                                                                                                                                                  , (unIData
                                                                                                                                                                                       (force
                                                                                                                                                                                          headList
                                                                                                                                                                                          l))
                                                                                                                                                                                  , (unIData
                                                                                                                                                                                       (force
                                                                                                                                                                                          headList
                                                                                                                                                                                          l))
                                                                                                                                                                                  , (unIData
                                                                                                                                                                                       (force
                                                                                                                                                                                          headList
                                                                                                                                                                                          l))
                                                                                                                                                                                  , (unIData
                                                                                                                                                                                       (force
                                                                                                                                                                                          headList
                                                                                                                                                                                          l))
                                                                                                                                                                                  , (unIData
                                                                                                                                                                                       (force
                                                                                                                                                                                          headList
                                                                                                                                                                                          (force
                                                                                                                                                                                             tailList
                                                                                                                                                                                             l))) ])
                                                                                                                                                                               (force
                                                                                                                                                                                  tailList
                                                                                                                                                                                  l))
                                                                                                                                                                            (force
                                                                                                                                                                               tailList
                                                                                                                                                                               l))
                                                                                                                                                                         (force
                                                                                                                                                                            tailList
                                                                                                                                                                            l))
                                                                                                                                                                      (force
                                                                                                                                                                         tailList
                                                                                                                                                                         l))
                                                                                                                                                                   (force
                                                                                                                                                                      tailList
                                                                                                                                                                      ds)) ]
                                                                                                                                                            args) ])) ])
                                                                                                                                        (force
                                                                                                                                           trace
                                                                                                                                           "Partial unlock requested"
                                                                                                                                           context)) ]))
                                                                                                                             (force
                                                                                                                                trace
                                                                                                                                "Parsed ScriptContext"
                                                                                                                                ctx))
                                                                                                                          [ (traceError
                                                                                                                               "PT5")
                                                                                                                          , () ]))
                                                                                                                    (\x
                                                                                                                      y ->
                                                                                                                       addInteger
                                                                                                                         1
                                                                                                                         (divideInteger
                                                                                                                            (subtractInteger
                                                                                                                               x
                                                                                                                               1)
                                                                                                                            y)))
                                                                                                                 (\ds
                                                                                                                   ds ->
                                                                                                                    (\tup ->
                                                                                                                       force
                                                                                                                         ((\fail ->
                                                                                                                             case
                                                                                                                               (equalsInteger
                                                                                                                                  `$bPubKeyCredential`
                                                                                                                                  (case
                                                                                                                                     tup
                                                                                                                                     [ (\l
                                                                                                                                         r ->
                                                                                                                                          l) ]))
                                                                                                                               [ (delay
                                                                                                                                    (fail
                                                                                                                                       ()))
                                                                                                                               , (delay
                                                                                                                                    ((\tup ->
                                                                                                                                        case
                                                                                                                                          (equalsInteger
                                                                                                                                             `$bPubKeyCredential`
                                                                                                                                             (case
                                                                                                                                                tup
                                                                                                                                                [ (\l
                                                                                                                                                    r ->
                                                                                                                                                     l) ]))
                                                                                                                                          [ (fail
                                                                                                                                               ())
                                                                                                                                          , (equalsByteString
                                                                                                                                               (unBData
                                                                                                                                                  (force
                                                                                                                                                     headList
                                                                                                                                                     (case
                                                                                                                                                        tup
                                                                                                                                                        [ (\l
                                                                                                                                                            r ->
                                                                                                                                                             r) ])))
                                                                                                                                               (unBData
                                                                                                                                                  (force
                                                                                                                                                     headList
                                                                                                                                                     (case
                                                                                                                                                        tup
                                                                                                                                                        [ (\l
                                                                                                                                                            r ->
                                                                                                                                                             r) ])))) ])
                                                                                                                                       (unConstrData
                                                                                                                                          ds))) ])
                                                                                                                            (\ds ->
                                                                                                                               (\tup ->
                                                                                                                                  case
                                                                                                                                    (equalsInteger
                                                                                                                                       `$bScriptCredential`
                                                                                                                                       (case
                                                                                                                                          tup
                                                                                                                                          [ (\l
                                                                                                                                              r ->
                                                                                                                                               l) ]))
                                                                                                                                    [ False
                                                                                                                                    , ((\tup ->
                                                                                                                                          case
                                                                                                                                            (equalsInteger
                                                                                                                                               `$bScriptCredential`
                                                                                                                                               (case
                                                                                                                                                  tup
                                                                                                                                                  [ (\l
                                                                                                                                                      r ->
                                                                                                                                                       l) ]))
                                                                                                                                            [ False
                                                                                                                                            , (equalsByteString
                                                                                                                                                 (unBData
                                                                                                                                                    (force
                                                                                                                                                       headList
                                                                                                                                                       (case
                                                                                                                                                          tup
                                                                                                                                                          [ (\l
                                                                                                                                                              r ->
                                                                                                                                                               r) ])))
                                                                                                                                                 (unBData
                                                                                                                                                    (force
                                                                                                                                                       headList
                                                                                                                                                       (case
                                                                                                                                                          tup
                                                                                                                                                          [ (\l
                                                                                                                                                              r ->
                                                                                                                                                               r) ])))) ])
                                                                                                                                         (unConstrData
                                                                                                                                            ds)) ])
                                                                                                                                 (unConstrData
                                                                                                                                    ds))))
                                                                                                                      (unConstrData
                                                                                                                         ds)))
                                                                                                              (\scrut
                                                                                                                cont
                                                                                                                fail ->
                                                                                                                 (\tup ->
                                                                                                                    case
                                                                                                                      (equalsInteger
                                                                                                                         `$bScriptCredential`
                                                                                                                         (case
                                                                                                                            tup
                                                                                                                            [ (\l
                                                                                                                                r ->
                                                                                                                                 l) ]))
                                                                                                                      [ (fail
                                                                                                                           ())
                                                                                                                      , ((\l ->
                                                                                                                            (\l ->
                                                                                                                               cont
                                                                                                                                 (unIData
                                                                                                                                    (force
                                                                                                                                       headList
                                                                                                                                       l))
                                                                                                                                 (unIData
                                                                                                                                    (force
                                                                                                                                       headList
                                                                                                                                       l))
                                                                                                                                 (unIData
                                                                                                                                    (force
                                                                                                                                       headList
                                                                                                                                       (force
                                                                                                                                          tailList
                                                                                                                                          l))))
                                                                                                                              (force
                                                                                                                                 tailList
                                                                                                                                 l))
                                                                                                                           (case
                                                                                                                              tup
                                                                                                                              [ (\l
                                                                                                                                  r ->
                                                                                                                                   r) ])) ])
                                                                                                                   (unConstrData
                                                                                                                      scrut)))
                                                                                                           0)
                                                                                                        2)
                                                                                                     1)
                                                                                                  (\ds ->
                                                                                                     unBData
                                                                                                       (force
                                                                                                          headList
                                                                                                          (case
                                                                                                             (unConstrData
                                                                                                                ds)
                                                                                                             [ (\l
                                                                                                                 r ->
                                                                                                                  r) ]))))
                                                                                               (\ds ->
                                                                                                  unIData
                                                                                                    (force
                                                                                                       headList
                                                                                                       (force
                                                                                                          tailList
                                                                                                          (case
                                                                                                             (unConstrData
                                                                                                                ds)
                                                                                                             [ (\l
                                                                                                                 r ->
                                                                                                                  r) ])))))
                                                                                            (\scrut
                                                                                              cont
                                                                                              fail ->
                                                                                               (\tup ->
                                                                                                  case
                                                                                                    (equalsInteger
                                                                                                       `$bPubKeyCredential`
                                                                                                       (case
                                                                                                          tup
                                                                                                          [ (\l
                                                                                                              r ->
                                                                                                               l) ]))
                                                                                                    [ (fail
                                                                                                         ())
                                                                                                    , (cont
                                                                                                         (unBData
                                                                                                            (force
                                                                                                               headList
                                                                                                               (case
                                                                                                                  tup
                                                                                                                  [ (\l
                                                                                                                      r ->
                                                                                                                       r) ])))) ])
                                                                                                 (unConstrData
                                                                                                    scrut)))
                                                                                         0)
                                                                                      (\scrut
                                                                                        cont
                                                                                        fail ->
                                                                                         (\tup ->
                                                                                            case
                                                                                              (equalsInteger
                                                                                                 1
                                                                                                 (case
                                                                                                    tup
                                                                                                    [ (\l
                                                                                                        r ->
                                                                                                         l) ]))
                                                                                              [ (fail
                                                                                                   ())
                                                                                              , ((\l ->
                                                                                                    cont
                                                                                                      (force
                                                                                                         headList
                                                                                                         l)
                                                                                                      (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                                                                                                         `$fUnsafeFromDataBuiltinData_$cunsafeFromBuiltinData`
                                                                                                         (force
                                                                                                            headList
                                                                                                            (force
                                                                                                               tailList
                                                                                                               l))))
                                                                                                   (case
                                                                                                      tup
                                                                                                      [ (\l
                                                                                                          r ->
                                                                                                           r) ])) ])
                                                                                           (unConstrData
                                                                                              scrut)))
                                                                                   (\d ->
                                                                                      d))
                                                                                ((\lookup'
                                                                                   v
                                                                                   ds ->
                                                                                    case
                                                                                      ds
                                                                                      [ (\c
                                                                                          t ->
                                                                                           case
                                                                                             (lookup'
                                                                                                (bData
                                                                                                   c)
                                                                                                v)
                                                                                             [ (\a ->
                                                                                                  (\m ->
                                                                                                     case
                                                                                                       (lookup'
                                                                                                          (bData
                                                                                                             t)
                                                                                                          m)
                                                                                                       [ (\a ->
                                                                                                            unIData
                                                                                                              a)
                                                                                                       , 0 ])
                                                                                                    (unMapData
                                                                                                       a))
                                                                                             , 0 ]) ])
                                                                                   (\k ->
                                                                                      (\go
                                                                                        m ->
                                                                                         go
                                                                                           m)
                                                                                        (fix1
                                                                                           (\go
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
                                                                                                       [ go
                                                                                                       , (\ds ->
                                                                                                            constr 0
                                                                                                              [ (case
                                                                                                                   hd
                                                                                                                   [ (\l
                                                                                                                       r ->
                                                                                                                        r) ]) ]) ])
                                                                                                , (constr 1
                                                                                                     [  ]) ])))))
                                                                             (\ds ->
                                                                                case
                                                                                  ds
                                                                                  [ (\ds
                                                                                      ds
                                                                                      ds
                                                                                      ds
                                                                                      ds
                                                                                      ds
                                                                                      ds ->
                                                                                       ds) ]))
                                                                          (\scrut
                                                                            cont
                                                                            fail ->
                                                                             (\tup ->
                                                                                case
                                                                                  (equalsInteger
                                                                                     `$bScriptCredential`
                                                                                     (case
                                                                                        tup
                                                                                        [ (\l
                                                                                            r ->
                                                                                             l) ]))
                                                                                  [ (fail
                                                                                       ())
                                                                                  , (cont
                                                                                       (unBData
                                                                                          (force
                                                                                             headList
                                                                                             (case
                                                                                                tup
                                                                                                [ (\l
                                                                                                    r ->
                                                                                                     r) ])))) ])
                                                                               (unConstrData
                                                                                  scrut)))
                                                                       1)
                                                                    (\ds ->
                                                                       force
                                                                         headList
                                                                         (case
                                                                            (unConstrData
                                                                               ds)
                                                                            [ (\l
                                                                                r ->
                                                                                 r) ])))
                                                                 (\ds ->
                                                                    (\l ->
                                                                       (\tup ->
                                                                          case
                                                                            (equalsInteger
                                                                               1
                                                                               (case
                                                                                  tup
                                                                                  [ (\l
                                                                                      r ->
                                                                                       l) ]))
                                                                            [ (traceError
                                                                                 "Time range not Finite")
                                                                            , ((\posixTime ->
                                                                                  case
                                                                                    (case
                                                                                       (unConstrData
                                                                                          (force
                                                                                             headList
                                                                                             (force
                                                                                                tailList
                                                                                                l)))
                                                                                       [ (\index
                                                                                           args ->
                                                                                            case
                                                                                              index
                                                                                              [ (\ds ->
                                                                                                   False)
                                                                                              , (\ds ->
                                                                                                   True) ]
                                                                                              args) ])
                                                                                    [ (addInteger
                                                                                         1
                                                                                         posixTime)
                                                                                    , posixTime ])
                                                                                 (unIData
                                                                                    (force
                                                                                       headList
                                                                                       (case
                                                                                          tup
                                                                                          [ (\l
                                                                                              r ->
                                                                                               r) ])))) ])
                                                                         (unConstrData
                                                                            (force
                                                                               headList
                                                                               l)))
                                                                      (case
                                                                         (unConstrData
                                                                            (force
                                                                               headList
                                                                               (case
                                                                                  (unConstrData
                                                                                     ds)
                                                                                  [ (\l
                                                                                      r ->
                                                                                       r) ])))
                                                                         [ (\l
                                                                             r ->
                                                                              r) ])))
                                                              (\str ->
                                                                 (\x -> error)
                                                                   (force trace
                                                                      str
                                                                      (constr 0
                                                                         []))))
                                                           (\ds ->
                                                              `$mScriptContext`
                                                                ds
                                                                (\ds ds ds ->
                                                                   ds)
                                                                (\void ->
                                                                   error)))
                                                        (\ds ->
                                                           `$mScriptContext`
                                                             ds
                                                             (\ds ds ds -> ds)
                                                             (\void -> error)))
                                                     (\scrut cont fail ->
                                                        (\l ->
                                                           (\l ->
                                                              cont
                                                                (force headList
                                                                   l)
                                                                (force headList
                                                                   l)
                                                                (force headList
                                                                   (force
                                                                      tailList
                                                                      l)))
                                                             (force tailList l))
                                                          (case
                                                             (unConstrData
                                                                scrut)
                                                             [(\l r -> r)])))
                                                  (\ds ->
                                                     case
                                                       ds
                                                       [ (\ds
                                                           ds
                                                           ds
                                                           ds
                                                           ds
                                                           ds
                                                           ds ->
                                                            ds) ]))
                                               (\ds ->
                                                  force headList
                                                    (force tailList
                                                       (case
                                                          (unConstrData ds)
                                                          [(\l r -> r)]))))
                                            (\ds ->
                                               `$mTxInfo`
                                                 ds
                                                 (\ds
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
                                                   ds
                                                   ds
                                                   ds
                                                   ds
                                                   ds ->
                                                    ds)
                                                 (\void -> error)))
                                         (\ds ->
                                            `$mTxOut`
                                              ds
                                              (\ds ds ds ds -> ds)
                                              (\void -> error)))
                                      (\ds ->
                                         `$mTxOut`
                                           ds
                                           (\ds ds ds ds -> ds)
                                           (\void -> error)))
                                   (\scrut
                                     cont
                                     fail ->
                                      (\l ->
                                         (\l ->
                                            (\l ->
                                               cont
                                                 (force headList l)
                                                 (unMapData (force headList l))
                                                 (force headList l)
                                                 (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                                                    unBData
                                                    (force headList
                                                       (force tailList l))))
                                              (force tailList l))
                                           (force tailList l))
                                        (case
                                           (unConstrData scrut)
                                           [(\l r -> r)])))
                                (\ds ->
                                   unMapData
                                     (force headList
                                        (force tailList
                                           (case
                                              (unConstrData ds)
                                              [(\l r -> r)])))))
                             (\ds k ->
                                `$mTxInfo`
                                  ds
                                  (\ds
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
                                    ds
                                    ds
                                    ds
                                    ds
                                    ds ->
                                     case
                                       (find
                                          unBData
                                          (\y -> equalsByteString k y)
                                          ds)
                                       [(\ds -> True), False])
                                  (\void ->
                                     (\defaultBody -> case error [defaultBody])
                                       error)))
                          (\scrut
                            cont
                            fail ->
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
                                                           (\l ->
                                                              (\l ->
                                                                 (\l ->
                                                                    (\l ->
                                                                       (\l ->
                                                                          cont
                                                                            (unListData
                                                                               (force
                                                                                  headList
                                                                                  l))
                                                                            (unListData
                                                                               (force
                                                                                  headList
                                                                                  l))
                                                                            (unListData
                                                                               (force
                                                                                  headList
                                                                                  l))
                                                                            (unIData
                                                                               (force
                                                                                  headList
                                                                                  l))
                                                                            (unMapData
                                                                               (force
                                                                                  headList
                                                                                  l))
                                                                            (unListData
                                                                               (force
                                                                                  headList
                                                                                  l))
                                                                            (unMapData
                                                                               (force
                                                                                  headList
                                                                                  l))
                                                                            (force
                                                                               headList
                                                                               l)
                                                                            (unListData
                                                                               (force
                                                                                  headList
                                                                                  l))
                                                                            (unMapData
                                                                               (force
                                                                                  headList
                                                                                  l))
                                                                            (unMapData
                                                                               (force
                                                                                  headList
                                                                                  l))
                                                                            (unBData
                                                                               (force
                                                                                  headList
                                                                                  l))
                                                                            (unMapData
                                                                               (force
                                                                                  headList
                                                                                  l))
                                                                            (unListData
                                                                               (force
                                                                                  headList
                                                                                  l))
                                                                            (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                                                                               unIData
                                                                               (force
                                                                                  headList
                                                                                  l))
                                                                            (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                                                                               unIData
                                                                               (force
                                                                                  headList
                                                                                  (force
                                                                                     tailList
                                                                                     l))))
                                                                         (force
                                                                            tailList
                                                                            l))
                                                                      (force
                                                                         tailList
                                                                         l))
                                                                   (force
                                                                      tailList
                                                                      l))
                                                                (force tailList
                                                                   l))
                                                             (force tailList l))
                                                          (force tailList l))
                                                       (force tailList l))
                                                    (force tailList l))
                                                 (force tailList l))
                                              (force tailList l))
                                           (force tailList l))
                                        (force tailList l))
                                     (force tailList l))
                                  (force tailList l))
                               (case (unConstrData scrut) [(\l r -> r)])))
                       (\`$dUnsafeFromData` d ->
                          case
                            (unConstrData d)
                            [ (\index args ->
                                 case
                                   index
                                   [ (\ds ->
                                        constr 0
                                          [ (`$dUnsafeFromData`
                                               (force headList ds)) ])
                                   , (\ds -> constr 1 []) ]
                                   args) ]))
                    (\`$dUnsafeFromData` pred' ->
                       (\go eta -> go eta)
                         (fix1
                            (\go ds ->
                               case
                                 ds
                                 [ (\x eta ->
                                      (\h ->
                                         case
                                           (pred' h)
                                           [(go eta), (constr 0 [h])])
                                        (`$dUnsafeFromData` x))
                                 , (constr 1 []) ]))))
                 (\ds -> case ds [(\ds ds ds ds ds ds ds -> ds)]))
            , (delay
                 ((\x -> error)
                    (force trace
                       "Failed to parse ScriptContext"
                       (constr 0 [])))) ]))
      (\f ->
         (\s ->
            f
              (\x ->
                 f
                   (\x ->
                      f
                        (\x ->
                           f
                             (\x ->
                                f
                                  (\x ->
                                     f
                                       (\x ->
                                          f
                                            (\x ->
                                               f
                                                 (\x ->
                                                    f
                                                      (\x ->
                                                         f
                                                           (\x ->
                                                              f
                                                                (\x ->
                                                                   f
                                                                     (\x ->
                                                                        s s x)
                                                                     x)
                                                                x)
                                                           x)
                                                      x)
                                                 x)
                                            x)
                                       x)
                                  x)
                             x)
                        x)
                   x))
           (\s -> f (\x -> s s x)))
      (Constr 0
         [ Constr 0
             [ List []
             , List []
             , List []
             , I 0
             , Map []
             , List []
             , Map []
             , Constr 0
                 [ Constr 0 [Constr 1 [I 110], Constr 1 []]
                 , Constr 0 [Constr 1 [I 1100], Constr 1 []] ]
             , List [B #]
             , Map []
             , Map []
             , B #058fdca70be67c74151cea3846be7f73342d92c0090b62c1052e6790ad83f145
             , Map []
             , List []
             , Constr 1 []
             , Constr 1 [] ]
         , Constr 1 []
         , Constr 1
             [ Constr 0
                 [ B #058fdca70be67c74151cea3846be7f73342d92c0090b62c1052e6790ad83f145
                 , I 0 ]
             , Constr 0
                 [ Constr 0
                     [ Constr 0 [Constr 0 [B #], Constr 1 []]
                     , Constr 0 [B #24, B #746573742d6173736574]
                     , I 1000
                     , I 0
                     , I 100
                     , I 10
                     , I 10 ] ] ] ])))