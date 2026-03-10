(program
   1.1.0
   ((\fix1 ->
       (\countInputsAtScript ->
          (\caseList' ->
             (\findInputByOutRef ->
                (\findOutputByAddress ->
                   (\txSignedBy'
                     scriptContextData ->
                      (\ctxFields ->
                         (\txInfoFields ->
                            (\txInfoFields ->
                               (\txInfoFields ->
                                  (\txSignatories ->
                                     (\txValidRange ->
                                        (\txOutputs ->
                                           (\txInputs ->
                                              (\redeemerTag ->
                                                 (\spendingInfo ->
                                                    (\ownRef ->
                                                       (\datumData ->
                                                          case
                                                            (force
                                                               trace
                                                               "Parsed ScriptContext"
                                                               (force
                                                                  trace
                                                                  "Parsed Redeemer"
                                                                  (case
                                                                     redeemerTag
                                                                     [ (force
                                                                          trace
                                                                          "Partial unlock requested"
                                                                          ((\currentTimeApproximation ->
                                                                              (\vdFields ->
                                                                                 (\vdFields ->
                                                                                    (\vdFields ->
                                                                                       (\vdFields ->
                                                                                          (\vdFields ->
                                                                                             (\vdFields ->
                                                                                                (\totalInstallments ->
                                                                                                   (\firstUnlockPossibleAfter ->
                                                                                                      (\vestingPeriodEnd ->
                                                                                                         (\vestingTimeRemaining ->
                                                                                                            (\timeBetweenTwoInstallments ->
                                                                                                               (\expectedRemainingQty ->
                                                                                                                  (\assetFields ->
                                                                                                                     (\assetCs ->
                                                                                                                        (\assetTn ->
                                                                                                                           (\findToken ->
                                                                                                                              (\findCurrency ->
                                                                                                                                 (\findToken ->
                                                                                                                                    (\findCurrency ->
                                                                                                                                       (\beneficiaryHash ->
                                                                                                                                          (\signed ->
                                                                                                                                             (\resolvedFields ->
                                                                                                                                                (\inputAddress ->
                                                                                                                                                   (\scriptHash ->
                                                                                                                                                      (\ownOutputFields ->
                                                                                                                                                         (\outputDatum ->
                                                                                                                                                            (\newRemainingQty ->
                                                                                                                                                               (\resolvedDatum ->
                                                                                                                                                                  (\oldRemainingQty ->
                                                                                                                                                                     case
                                                                                                                                                                       signed
                                                                                                                                                                       [ ((\x ->
                                                                                                                                                                             error)
                                                                                                                                                                            (force
                                                                                                                                                                               trace
                                                                                                                                                                               "Missing beneficiary signature"
                                                                                                                                                                               (constr 0
                                                                                                                                                                                  [  ])))
                                                                                                                                                                       , (case
                                                                                                                                                                            (lessThanEqualsInteger
                                                                                                                                                                               currentTimeApproximation
                                                                                                                                                                               firstUnlockPossibleAfter)
                                                                                                                                                                            [ (case
                                                                                                                                                                                 (lessThanEqualsInteger
                                                                                                                                                                                    newRemainingQty
                                                                                                                                                                                    0)
                                                                                                                                                                                 [ (case
                                                                                                                                                                                      (lessThanEqualsInteger
                                                                                                                                                                                         oldRemainingQty
                                                                                                                                                                                         newRemainingQty)
                                                                                                                                                                                      [ (case
                                                                                                                                                                                           (equalsInteger
                                                                                                                                                                                              expectedRemainingQty
                                                                                                                                                                                              newRemainingQty)
                                                                                                                                                                                           [ ((\x ->
                                                                                                                                                                                                 error)
                                                                                                                                                                                                (force
                                                                                                                                                                                                   trace
                                                                                                                                                                                                   "Mismatched remaining asset"
                                                                                                                                                                                                   (constr 0
                                                                                                                                                                                                      [  ])))
                                                                                                                                                                                           , (case
                                                                                                                                                                                                (equalsData
                                                                                                                                                                                                   resolvedDatum
                                                                                                                                                                                                   outputDatum)
                                                                                                                                                                                                [ ((\x ->
                                                                                                                                                                                                      error)
                                                                                                                                                                                                     (force
                                                                                                                                                                                                        trace
                                                                                                                                                                                                        "Datum Modification Prohibited"
                                                                                                                                                                                                        (constr 0
                                                                                                                                                                                                           [  ])))
                                                                                                                                                                                                , (case
                                                                                                                                                                                                     (equalsInteger
                                                                                                                                                                                                        1
                                                                                                                                                                                                        (countInputsAtScript
                                                                                                                                                                                                           scriptHash
                                                                                                                                                                                                           txInputs))
                                                                                                                                                                                                     [ ((\x ->
                                                                                                                                                                                                           error)
                                                                                                                                                                                                          (force
                                                                                                                                                                                                             trace
                                                                                                                                                                                                             "Double satisfaction"
                                                                                                                                                                                                             (constr 0
                                                                                                                                                                                                                [  ])))
                                                                                                                                                                                                     , True ]) ]) ])
                                                                                                                                                                                      , ((\x ->
                                                                                                                                                                                            error)
                                                                                                                                                                                           (force
                                                                                                                                                                                              trace
                                                                                                                                                                                              "Remaining asset is not decreasing"
                                                                                                                                                                                              (constr 0
                                                                                                                                                                                                 [  ]))) ])
                                                                                                                                                                                 , ((\x ->
                                                                                                                                                                                       error)
                                                                                                                                                                                      (force
                                                                                                                                                                                         trace
                                                                                                                                                                                         "Zero remaining assets not allowed"
                                                                                                                                                                                         (constr 0
                                                                                                                                                                                            [  ]))) ])
                                                                                                                                                                            , ((\x ->
                                                                                                                                                                                  error)
                                                                                                                                                                                 (force
                                                                                                                                                                                    trace
                                                                                                                                                                                    "Unlock not permitted until firstUnlockPossibleAfter time"
                                                                                                                                                                                    (constr 0
                                                                                                                                                                                       [  ]))) ]) ])
                                                                                                                                                                    (findCurrency
                                                                                                                                                                       (unMapData
                                                                                                                                                                          (force
                                                                                                                                                                             headList
                                                                                                                                                                             (force
                                                                                                                                                                                tailList
                                                                                                                                                                                resolvedFields)))))
                                                                                                                                                                 (force
                                                                                                                                                                    headList
                                                                                                                                                                    (force
                                                                                                                                                                       tailList
                                                                                                                                                                       (force
                                                                                                                                                                          tailList
                                                                                                                                                                          resolvedFields))))
                                                                                                                                                              (findCurrency
                                                                                                                                                                 (unMapData
                                                                                                                                                                    (force
                                                                                                                                                                       headList
                                                                                                                                                                       (force
                                                                                                                                                                          tailList
                                                                                                                                                                          ownOutputFields)))))
                                                                                                                                                           (force
                                                                                                                                                              headList
                                                                                                                                                              (force
                                                                                                                                                                 tailList
                                                                                                                                                                 (force
                                                                                                                                                                    tailList
                                                                                                                                                                    ownOutputFields))))
                                                                                                                                                        (case
                                                                                                                                                           (unConstrData
                                                                                                                                                              (findOutputByAddress
                                                                                                                                                                 inputAddress
                                                                                                                                                                 txOutputs))
                                                                                                                                                           [ (\l
                                                                                                                                                               r ->
                                                                                                                                                                r) ]))
                                                                                                                                                     (unBData
                                                                                                                                                        (force
                                                                                                                                                           headList
                                                                                                                                                           (case
                                                                                                                                                              (unConstrData
                                                                                                                                                                 (force
                                                                                                                                                                    headList
                                                                                                                                                                    (case
                                                                                                                                                                       (unConstrData
                                                                                                                                                                          inputAddress)
                                                                                                                                                                       [ (\l
                                                                                                                                                                           r ->
                                                                                                                                                                            r) ])))
                                                                                                                                                              [ (\l
                                                                                                                                                                  r ->
                                                                                                                                                                   r) ]))))
                                                                                                                                                  (force
                                                                                                                                                     headList
                                                                                                                                                     resolvedFields))
                                                                                                                                               (case
                                                                                                                                                  (unConstrData
                                                                                                                                                     (force
                                                                                                                                                        headList
                                                                                                                                                        (force
                                                                                                                                                           tailList
                                                                                                                                                           (case
                                                                                                                                                              (unConstrData
                                                                                                                                                                 (findInputByOutRef
                                                                                                                                                                    ownRef
                                                                                                                                                                    txInputs))
                                                                                                                                                              [ (\l
                                                                                                                                                                  r ->
                                                                                                                                                                   r) ]))))
                                                                                                                                                  [ (\l
                                                                                                                                                      r ->
                                                                                                                                                       r) ]))
                                                                                                                                            (txSignedBy'
                                                                                                                                               txSignatories
                                                                                                                                               beneficiaryHash))
                                                                                                                                         (unBData
                                                                                                                                            (force
                                                                                                                                               headList
                                                                                                                                               (case
                                                                                                                                                  (unConstrData
                                                                                                                                                     (force
                                                                                                                                                        headList
                                                                                                                                                        (case
                                                                                                                                                           (unConstrData
                                                                                                                                                              (force
                                                                                                                                                                 headList
                                                                                                                                                                 vdFields))
                                                                                                                                                           [ (\l
                                                                                                                                                               r ->
                                                                                                                                                                r) ])))
                                                                                                                                                  [ (\l
                                                                                                                                                      r ->
                                                                                                                                                       r) ]))))
                                                                                                                                      (fix1
                                                                                                                                         (\findCurrency
                                                                                                                                           pairs ->
                                                                                                                                            case
                                                                                                                                              (force
                                                                                                                                                 nullList
                                                                                                                                                 pairs)
                                                                                                                                              [ ((\pair ->
                                                                                                                                                    case
                                                                                                                                                      (equalsByteString
                                                                                                                                                         (unBData
                                                                                                                                                            (case
                                                                                                                                                               pair
                                                                                                                                                               [ (\l
                                                                                                                                                                   r ->
                                                                                                                                                                    l) ]))
                                                                                                                                                         assetCs)
                                                                                                                                                      [ (findCurrency
                                                                                                                                                           (force
                                                                                                                                                              tailList
                                                                                                                                                              pairs))
                                                                                                                                                      , (findToken
                                                                                                                                                           (unMapData
                                                                                                                                                              (case
                                                                                                                                                                 pair
                                                                                                                                                                 [ (\l
                                                                                                                                                                     r ->
                                                                                                                                                                      r) ]))) ])
                                                                                                                                                   (force
                                                                                                                                                      headList
                                                                                                                                                      pairs))
                                                                                                                                              , 0 ])))
                                                                                                                                   (fix1
                                                                                                                                      (\findToken
                                                                                                                                        pairs ->
                                                                                                                                         case
                                                                                                                                           (force
                                                                                                                                              nullList
                                                                                                                                              pairs)
                                                                                                                                           [ ((\pair ->
                                                                                                                                                 case
                                                                                                                                                   (equalsByteString
                                                                                                                                                      (unBData
                                                                                                                                                         (case
                                                                                                                                                            pair
                                                                                                                                                            [ (\l
                                                                                                                                                                r ->
                                                                                                                                                                 l) ]))
                                                                                                                                                      assetTn)
                                                                                                                                                   [ (findToken
                                                                                                                                                        (force
                                                                                                                                                           tailList
                                                                                                                                                           pairs))
                                                                                                                                                   , (unIData
                                                                                                                                                        (case
                                                                                                                                                           pair
                                                                                                                                                           [ (\l
                                                                                                                                                               r ->
                                                                                                                                                                r) ])) ])
                                                                                                                                                (force
                                                                                                                                                   headList
                                                                                                                                                   pairs))
                                                                                                                                           , 0 ])))
                                                                                                                                (fix1
                                                                                                                                   (\findCurrency
                                                                                                                                     pairs ->
                                                                                                                                      case
                                                                                                                                        (force
                                                                                                                                           nullList
                                                                                                                                           pairs)
                                                                                                                                        [ ((\pair ->
                                                                                                                                              case
                                                                                                                                                (equalsByteString
                                                                                                                                                   (unBData
                                                                                                                                                      (case
                                                                                                                                                         pair
                                                                                                                                                         [ (\l
                                                                                                                                                             r ->
                                                                                                                                                              l) ]))
                                                                                                                                                   assetCs)
                                                                                                                                                [ (findCurrency
                                                                                                                                                     (force
                                                                                                                                                        tailList
                                                                                                                                                        pairs))
                                                                                                                                                , (findToken
                                                                                                                                                     (unMapData
                                                                                                                                                        (case
                                                                                                                                                           pair
                                                                                                                                                           [ (\l
                                                                                                                                                               r ->
                                                                                                                                                                r) ]))) ])
                                                                                                                                             (force
                                                                                                                                                headList
                                                                                                                                                pairs))
                                                                                                                                        , 0 ])))
                                                                                                                             (fix1
                                                                                                                                (\findToken
                                                                                                                                  pairs ->
                                                                                                                                   case
                                                                                                                                     (force
                                                                                                                                        nullList
                                                                                                                                        pairs)
                                                                                                                                     [ ((\pair ->
                                                                                                                                           case
                                                                                                                                             (equalsByteString
                                                                                                                                                (unBData
                                                                                                                                                   (case
                                                                                                                                                      pair
                                                                                                                                                      [ (\l
                                                                                                                                                          r ->
                                                                                                                                                           l) ]))
                                                                                                                                                assetTn)
                                                                                                                                             [ (findToken
                                                                                                                                                  (force
                                                                                                                                                     tailList
                                                                                                                                                     pairs))
                                                                                                                                             , (unIData
                                                                                                                                                  (case
                                                                                                                                                     pair
                                                                                                                                                     [ (\l
                                                                                                                                                         r ->
                                                                                                                                                          r) ])) ])
                                                                                                                                          (force
                                                                                                                                             headList
                                                                                                                                             pairs))
                                                                                                                                     , 0 ])))
                                                                                                                          (unBData
                                                                                                                             (force
                                                                                                                                headList
                                                                                                                                (force
                                                                                                                                   tailList
                                                                                                                                   assetFields))))
                                                                                                                       (unBData
                                                                                                                          (force
                                                                                                                             headList
                                                                                                                             assetFields)))
                                                                                                                    (case
                                                                                                                       (unConstrData
                                                                                                                          (force
                                                                                                                             headList
                                                                                                                             vdFields))
                                                                                                                       [ (\l
                                                                                                                           r ->
                                                                                                                            r) ]))
                                                                                                                 (addInteger
                                                                                                                    1
                                                                                                                    (divideInteger
                                                                                                                       (subtractInteger
                                                                                                                          (multiplyInteger
                                                                                                                             (addInteger
                                                                                                                                1
                                                                                                                                (divideInteger
                                                                                                                                   (subtractInteger
                                                                                                                                      vestingTimeRemaining
                                                                                                                                      1)
                                                                                                                                   timeBetweenTwoInstallments))
                                                                                                                             (unIData
                                                                                                                                (force
                                                                                                                                   headList
                                                                                                                                   vdFields)))
                                                                                                                          1)
                                                                                                                       totalInstallments)))
                                                                                                              (addInteger
                                                                                                                 1
                                                                                                                 (divideInteger
                                                                                                                    (subtractInteger
                                                                                                                       (subtractInteger
                                                                                                                          vestingPeriodEnd
                                                                                                                          (unIData
                                                                                                                             (force
                                                                                                                                headList
                                                                                                                                vdFields)))
                                                                                                                       1)
                                                                                                                    totalInstallments)))
                                                                                                           (subtractInteger
                                                                                                              vestingPeriodEnd
                                                                                                              currentTimeApproximation))
                                                                                                        (unIData
                                                                                                           (force
                                                                                                              headList
                                                                                                              vdFields)))
                                                                                                     (unIData
                                                                                                        (force
                                                                                                           headList
                                                                                                           vdFields)))
                                                                                                  (unIData
                                                                                                     (force
                                                                                                        headList
                                                                                                        (force
                                                                                                           tailList
                                                                                                           vdFields))))
                                                                                               (force
                                                                                                  tailList
                                                                                                  vdFields))
                                                                                            (force
                                                                                               tailList
                                                                                               vdFields))
                                                                                         (force
                                                                                            tailList
                                                                                            vdFields))
                                                                                      (force
                                                                                         tailList
                                                                                         vdFields))
                                                                                   (force
                                                                                      tailList
                                                                                      vdFields))
                                                                                (case
                                                                                   (unConstrData
                                                                                      datumData)
                                                                                   [ (\l
                                                                                       r ->
                                                                                        r) ]))
                                                                             ((\lowerFields ->
                                                                                 (\extCon ->
                                                                                    (\extTag ->
                                                                                       (\extFields ->
                                                                                          (\offset ->
                                                                                             case
                                                                                               (equalsInteger
                                                                                                  1
                                                                                                  extTag)
                                                                                               [ ((\x ->
                                                                                                     error)
                                                                                                    (force
                                                                                                       trace
                                                                                                       "Time range not Finite"
                                                                                                       (constr 0
                                                                                                          [  ])))
                                                                                               , (addInteger
                                                                                                    (unIData
                                                                                                       (force
                                                                                                          headList
                                                                                                          extFields))
                                                                                                    offset) ])
                                                                                            (case
                                                                                               (equalsInteger
                                                                                                  1
                                                                                                  (case
                                                                                                     (unConstrData
                                                                                                        (force
                                                                                                           headList
                                                                                                           (force
                                                                                                              tailList
                                                                                                              lowerFields)))
                                                                                                     [ (\l
                                                                                                         r ->
                                                                                                          l) ]))
                                                                                               [ 1
                                                                                               , 0 ]))
                                                                                         (case
                                                                                            extCon
                                                                                            [ (\l
                                                                                                r ->
                                                                                                 r) ]))
                                                                                      (case
                                                                                         extCon
                                                                                         [ (\l
                                                                                             r ->
                                                                                              l) ]))
                                                                                   (unConstrData
                                                                                      (force
                                                                                         headList
                                                                                         lowerFields)))
                                                                                (case
                                                                                   (unConstrData
                                                                                      (force
                                                                                         headList
                                                                                         (case
                                                                                            (unConstrData
                                                                                               txValidRange)
                                                                                            [ (\l
                                                                                                r ->
                                                                                                 r) ])))
                                                                                   [ (\l
                                                                                       r ->
                                                                                        r) ]))))
                                                                     , (force
                                                                          trace
                                                                          "Full unlock requested"
                                                                          ((\currentTimeApproximation ->
                                                                              (\vdFields ->
                                                                                 (\vestingPeriodEnd ->
                                                                                    (\beneficiaryHash ->
                                                                                       case
                                                                                         (txSignedBy'
                                                                                            txSignatories
                                                                                            beneficiaryHash)
                                                                                         [ ((\x ->
                                                                                               error)
                                                                                              (force
                                                                                                 trace
                                                                                                 "Missing beneficiary signature"
                                                                                                 (constr 0
                                                                                                    [  ])))
                                                                                         , (case
                                                                                              (lessThanEqualsInteger
                                                                                                 currentTimeApproximation
                                                                                                 vestingPeriodEnd)
                                                                                              [ True
                                                                                              , ((\x ->
                                                                                                    error)
                                                                                                   (force
                                                                                                      trace
                                                                                                      "Unlock not permitted until vestingPeriodEnd time"
                                                                                                      (constr 0
                                                                                                         [  ]))) ]) ])
                                                                                      (unBData
                                                                                         (force
                                                                                            headList
                                                                                            (case
                                                                                               (unConstrData
                                                                                                  (force
                                                                                                     headList
                                                                                                     (case
                                                                                                        (unConstrData
                                                                                                           (force
                                                                                                              headList
                                                                                                              vdFields))
                                                                                                        [ (\l
                                                                                                            r ->
                                                                                                             r) ])))
                                                                                               [ (\l
                                                                                                   r ->
                                                                                                    r) ]))))
                                                                                   (unIData
                                                                                      (force
                                                                                         headList
                                                                                         (force
                                                                                            tailList
                                                                                            (force
                                                                                               tailList
                                                                                               (force
                                                                                                  tailList
                                                                                                  (force
                                                                                                     tailList
                                                                                                     vdFields)))))))
                                                                                (case
                                                                                   (unConstrData
                                                                                      datumData)
                                                                                   [ (\l
                                                                                       r ->
                                                                                        r) ]))
                                                                             ((\lowerFields ->
                                                                                 (\extCon ->
                                                                                    (\extTag ->
                                                                                       (\extFields ->
                                                                                          (\offset ->
                                                                                             case
                                                                                               (equalsInteger
                                                                                                  1
                                                                                                  extTag)
                                                                                               [ ((\x ->
                                                                                                     error)
                                                                                                    (force
                                                                                                       trace
                                                                                                       "Time range not Finite"
                                                                                                       (constr 0
                                                                                                          [  ])))
                                                                                               , (addInteger
                                                                                                    (unIData
                                                                                                       (force
                                                                                                          headList
                                                                                                          extFields))
                                                                                                    offset) ])
                                                                                            (case
                                                                                               (equalsInteger
                                                                                                  1
                                                                                                  (case
                                                                                                     (unConstrData
                                                                                                        (force
                                                                                                           headList
                                                                                                           (force
                                                                                                              tailList
                                                                                                              lowerFields)))
                                                                                                     [ (\l
                                                                                                         r ->
                                                                                                          l) ]))
                                                                                               [ 1
                                                                                               , 0 ]))
                                                                                         (case
                                                                                            extCon
                                                                                            [ (\l
                                                                                                r ->
                                                                                                 r) ]))
                                                                                      (case
                                                                                         extCon
                                                                                         [ (\l
                                                                                             r ->
                                                                                              l) ]))
                                                                                   (unConstrData
                                                                                      (force
                                                                                         headList
                                                                                         lowerFields)))
                                                                                (case
                                                                                   (unConstrData
                                                                                      (force
                                                                                         headList
                                                                                         (case
                                                                                            (unConstrData
                                                                                               txValidRange)
                                                                                            [ (\l
                                                                                                r ->
                                                                                                 r) ])))
                                                                                   [ (\l
                                                                                       r ->
                                                                                        r) ])))) ])))
                                                            [ ((\x ->
                                                                  error)
                                                                 (force
                                                                    trace
                                                                    "Validation failed"
                                                                    (constr 0
                                                                       [])))
                                                            , (force
                                                                 trace
                                                                 "Validation completed"
                                                                 ()) ])
                                                         (case
                                                            spendingInfo
                                                            [(\l r -> r)]))
                                                      (case
                                                         spendingInfo
                                                         [(\l r -> l)]))
                                                   ((\con ->
                                                       (\tag ->
                                                          (\fields ->
                                                             case
                                                               (equalsInteger
                                                                  1
                                                                  tag)
                                                               [ ((\x ->
                                                                     error)
                                                                    (force
                                                                       trace
                                                                       "Not spending script"
                                                                       (constr 0
                                                                          [])))
                                                               , ((\mdCon ->
                                                                     (\mdTag ->
                                                                        (\mdFields ->
                                                                           (\ownRef ->
                                                                              case
                                                                                (equalsInteger
                                                                                   0
                                                                                   mdTag)
                                                                                [ ((\x ->
                                                                                      error)
                                                                                     (force
                                                                                        trace
                                                                                        "Missing datum"
                                                                                        (constr 0
                                                                                           [  ])))
                                                                                , (mkPairData
                                                                                     ownRef
                                                                                     (force
                                                                                        headList
                                                                                        mdFields)) ])
                                                                             (force
                                                                                headList
                                                                                fields))
                                                                          (case
                                                                             mdCon
                                                                             [ (\l
                                                                                 r ->
                                                                                  r) ]))
                                                                       (case
                                                                          mdCon
                                                                          [ (\l
                                                                              r ->
                                                                               l) ]))
                                                                    (unConstrData
                                                                       (force
                                                                          headList
                                                                          (force
                                                                             tailList
                                                                             fields)))) ])
                                                            (case
                                                               con
                                                               [(\l r -> r)]))
                                                         (case
                                                            con
                                                            [(\l r -> l)]))
                                                      (unConstrData
                                                         (force
                                                            headList
                                                            (force
                                                               tailList
                                                               (force
                                                                  tailList
                                                                  ctxFields))))))
                                                (case
                                                   (unConstrData
                                                      (force headList
                                                         (force tailList
                                                            ctxFields)))
                                                   [(\l r -> l)]))
                                             (unListData
                                                (force headList txInfoFields)))
                                          (unListData
                                             (force headList txInfoFields)))
                                       (force headList txInfoFields))
                                    (unListData
                                       (force headList
                                          (force tailList txInfoFields))))
                                 (force tailList
                                    (force tailList
                                       (force tailList
                                          (force tailList
                                             (force tailList txInfoFields))))))
                              (force tailList (force tailList txInfoFields)))
                           (case
                              (unConstrData (force headList ctxFields))
                              [(\l r -> r)]))
                        (case
                           (unConstrData
                              (force trace
                                 "Parsing ScriptContext..."
                                 scriptContextData))
                           [(\l r -> r)]))
                     (fix1
                        (\txSignedBy' signatories pkh ->
                           case
                             signatories
                             [ (\s ss ->
                                  case
                                    (equalsByteString (unBData s) pkh)
                                    [(txSignedBy' ss pkh), True])
                             , False ])))
                  (fix1
                     (\findOutputByAddress addr outputs ->
                        case
                          (constr 0
                             [ ((\x -> error)
                                  (force trace
                                     "Own output not found"
                                     (constr 0 [])))
                             , (\out outs ->
                                  case
                                    (equalsData
                                       (force headList
                                          (case
                                             (unConstrData out)
                                             [(\l r -> r)]))
                                       addr)
                                    [(findOutputByAddress addr outs), out])
                             , outputs ])
                          [caseList'])))
               (fix1
                  (\findInputByOutRef ref inputs ->
                     case
                       (constr 0
                          [ ((\x -> error)
                               (force trace
                                  "Own input not found"
                                  (constr 0 [])))
                          , (\txIn txIns ->
                               case
                                 (equalsData
                                    (force headList
                                       (case (unConstrData txIn) [(\l r -> r)]))
                                    ref)
                                 [(findInputByOutRef ref txIns), txIn])
                          , inputs ])
                       [caseList'])))
            (\z f xs -> case xs [f, z]))
         (fix1
            (\countInputsAtScript scriptHash inputs ->
               case
                 inputs
                 [ (\txIn txIns ->
                      (\rest ->
                         (\credCon ->
                            (\credTag ->
                               (\credFields ->
                                  case
                                    (equalsInteger 1 credTag)
                                    [ rest
                                    , (case
                                         (equalsByteString
                                            (unBData
                                               (force headList credFields))
                                            scriptHash)
                                         [rest, (addInteger 1 rest)]) ])
                                 (case credCon [(\l r -> r)]))
                              (case credCon [(\l r -> l)]))
                           (unConstrData
                              (force headList
                                 (case
                                    (unConstrData
                                       (force headList
                                          (case
                                             (unConstrData
                                                (force headList
                                                   (force tailList
                                                      (case
                                                         (unConstrData txIn)
                                                         [(\l r -> r)]))))
                                             [(\l r -> r)])))
                                    [(\l r -> r)]))))
                        (countInputsAtScript scriptHash txIns))
                 , 0 ])))
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
             [ List
                 [ Constr 0
                     [ Constr 0
                         [ B #058fdca70be67c74151cea3846be7f73342d92c0090b62c1052e6790ad83f145
                         , I 0 ]
                     , Constr 0
                         [ Constr 0
                             [Constr 1 [B #6465616462656566], Constr 1 []]
                         , Map []
                         , Constr 2
                             [ Constr 0
                                 [ Constr 0 [Constr 0 [B #], Constr 1 []]
                                 , Constr 0 [B #24, B #746573742d6173736574]
                                 , I 1000
                                 , I 0
                                 , I 100
                                 , I 10
                                 , I 10 ] ]
                         , Constr 1 [] ] ] ]
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
             , Map
                 [ ( Constr 1
                       [ Constr 0
                           [ B #058fdca70be67c74151cea3846be7f73342d92c0090b62c1052e6790ad83f145
                           , I 0 ] ]
                 , Constr 1 [] ) ]
             , Map []
             , B #6465616462656566
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