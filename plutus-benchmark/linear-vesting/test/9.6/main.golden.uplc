(program
   1.1.0
   (case
      (constr 0
         [(force nullList), (force tailList), (force headList), (force trace)])
      [ (\forced
          forced
          forced
          forced ->
           (\fix1 ->
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
                                                                   (forced
                                                                      "Parsed ScriptContext"
                                                                      (forced
                                                                         "Parsed Redeemer"
                                                                         (case
                                                                            redeemerTag
                                                                            [ (forced
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
                                                                                                                                                                                   (forced
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
                                                                                                                                                                                                       (forced
                                                                                                                                                                                                          "Mismatched remaining asset"
                                                                                                                                                                                                          (constr 0
                                                                                                                                                                                                             [  ])))
                                                                                                                                                                                                  , (case
                                                                                                                                                                                                       (equalsData
                                                                                                                                                                                                          resolvedDatum
                                                                                                                                                                                                          outputDatum)
                                                                                                                                                                                                       [ ((\x ->
                                                                                                                                                                                                             error)
                                                                                                                                                                                                            (forced
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
                                                                                                                                                                                                                 (forced
                                                                                                                                                                                                                    "Double satisfaction"
                                                                                                                                                                                                                    (constr 0
                                                                                                                                                                                                                       [  ])))
                                                                                                                                                                                                            , True ]) ]) ])
                                                                                                                                                                                             , ((\x ->
                                                                                                                                                                                                   error)
                                                                                                                                                                                                  (forced
                                                                                                                                                                                                     "Remaining asset is not decreasing"
                                                                                                                                                                                                     (constr 0
                                                                                                                                                                                                        [  ]))) ])
                                                                                                                                                                                        , ((\x ->
                                                                                                                                                                                              error)
                                                                                                                                                                                             (forced
                                                                                                                                                                                                "Zero remaining assets not allowed"
                                                                                                                                                                                                (constr 0
                                                                                                                                                                                                   [  ]))) ])
                                                                                                                                                                                   , ((\x ->
                                                                                                                                                                                         error)
                                                                                                                                                                                        (forced
                                                                                                                                                                                           "Unlock not permitted until firstUnlockPossibleAfter time"
                                                                                                                                                                                           (constr 0
                                                                                                                                                                                              [  ]))) ]) ])
                                                                                                                                                                           (findCurrency
                                                                                                                                                                              (unMapData
                                                                                                                                                                                 (forced
                                                                                                                                                                                    (forced
                                                                                                                                                                                       resolvedFields)))))
                                                                                                                                                                        (forced
                                                                                                                                                                           (forced
                                                                                                                                                                              (forced
                                                                                                                                                                                 resolvedFields))))
                                                                                                                                                                     (findCurrency
                                                                                                                                                                        (unMapData
                                                                                                                                                                           (forced
                                                                                                                                                                              (forced
                                                                                                                                                                                 ownOutputFields)))))
                                                                                                                                                                  (forced
                                                                                                                                                                     (forced
                                                                                                                                                                        (forced
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
                                                                                                                                                               (forced
                                                                                                                                                                  (case
                                                                                                                                                                     (unConstrData
                                                                                                                                                                        (forced
                                                                                                                                                                           (case
                                                                                                                                                                              (unConstrData
                                                                                                                                                                                 inputAddress)
                                                                                                                                                                              [ (\l
                                                                                                                                                                                  r ->
                                                                                                                                                                                   r) ])))
                                                                                                                                                                     [ (\l
                                                                                                                                                                         r ->
                                                                                                                                                                          r) ]))))
                                                                                                                                                         (forced
                                                                                                                                                            resolvedFields))
                                                                                                                                                      (case
                                                                                                                                                         (unConstrData
                                                                                                                                                            (forced
                                                                                                                                                               (forced
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
                                                                                                                                                   (forced
                                                                                                                                                      (case
                                                                                                                                                         (unConstrData
                                                                                                                                                            (forced
                                                                                                                                                               (case
                                                                                                                                                                  (unConstrData
                                                                                                                                                                     (forced
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
                                                                                                                                                     (forced
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
                                                                                                                                                                  (forced
                                                                                                                                                                     pairs))
                                                                                                                                                             , (findToken
                                                                                                                                                                  (unMapData
                                                                                                                                                                     (case
                                                                                                                                                                        pair
                                                                                                                                                                        [ (\l
                                                                                                                                                                            r ->
                                                                                                                                                                             r) ]))) ])
                                                                                                                                                          (forced
                                                                                                                                                             pairs))
                                                                                                                                                     , 0 ])))
                                                                                                                                          (fix1
                                                                                                                                             (\findToken
                                                                                                                                               pairs ->
                                                                                                                                                case
                                                                                                                                                  (forced
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
                                                                                                                                                               (forced
                                                                                                                                                                  pairs))
                                                                                                                                                          , (unIData
                                                                                                                                                               (case
                                                                                                                                                                  pair
                                                                                                                                                                  [ (\l
                                                                                                                                                                      r ->
                                                                                                                                                                       r) ])) ])
                                                                                                                                                       (forced
                                                                                                                                                          pairs))
                                                                                                                                                  , 0 ])))
                                                                                                                                       (fix1
                                                                                                                                          (\findCurrency
                                                                                                                                            pairs ->
                                                                                                                                             case
                                                                                                                                               (forced
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
                                                                                                                                                            (forced
                                                                                                                                                               pairs))
                                                                                                                                                       , (findToken
                                                                                                                                                            (unMapData
                                                                                                                                                               (case
                                                                                                                                                                  pair
                                                                                                                                                                  [ (\l
                                                                                                                                                                      r ->
                                                                                                                                                                       r) ]))) ])
                                                                                                                                                    (forced
                                                                                                                                                       pairs))
                                                                                                                                               , 0 ])))
                                                                                                                                    (fix1
                                                                                                                                       (\findToken
                                                                                                                                         pairs ->
                                                                                                                                          case
                                                                                                                                            (forced
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
                                                                                                                                                         (forced
                                                                                                                                                            pairs))
                                                                                                                                                    , (unIData
                                                                                                                                                         (case
                                                                                                                                                            pair
                                                                                                                                                            [ (\l
                                                                                                                                                                r ->
                                                                                                                                                                 r) ])) ])
                                                                                                                                                 (forced
                                                                                                                                                    pairs))
                                                                                                                                            , 0 ])))
                                                                                                                                 (unBData
                                                                                                                                    (forced
                                                                                                                                       (forced
                                                                                                                                          assetFields))))
                                                                                                                              (unBData
                                                                                                                                 (forced
                                                                                                                                    assetFields)))
                                                                                                                           (case
                                                                                                                              (unConstrData
                                                                                                                                 (forced
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
                                                                                                                                       (forced
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
                                                                                                                                    (forced
                                                                                                                                       vdFields)))
                                                                                                                              1)
                                                                                                                           totalInstallments)))
                                                                                                                  (subtractInteger
                                                                                                                     vestingPeriodEnd
                                                                                                                     currentTimeApproximation))
                                                                                                               (unIData
                                                                                                                  (forced
                                                                                                                     vdFields)))
                                                                                                            (unIData
                                                                                                               (forced
                                                                                                                  vdFields)))
                                                                                                         (unIData
                                                                                                            (forced
                                                                                                               (forced
                                                                                                                  vdFields))))
                                                                                                      (forced
                                                                                                         vdFields))
                                                                                                   (forced
                                                                                                      vdFields))
                                                                                                (forced
                                                                                                   vdFields))
                                                                                             (forced
                                                                                                vdFields))
                                                                                          (forced
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
                                                                                                           (forced
                                                                                                              "Time range not Finite"
                                                                                                              (constr 0
                                                                                                                 [  ])))
                                                                                                      , (addInteger
                                                                                                           (unIData
                                                                                                              (forced
                                                                                                                 extFields))
                                                                                                           offset) ])
                                                                                                   (case
                                                                                                      (equalsInteger
                                                                                                         1
                                                                                                         (case
                                                                                                            (unConstrData
                                                                                                               (forced
                                                                                                                  (forced
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
                                                                                             (forced
                                                                                                lowerFields)))
                                                                                       (case
                                                                                          (unConstrData
                                                                                             (forced
                                                                                                (case
                                                                                                   (unConstrData
                                                                                                      txValidRange)
                                                                                                   [ (\l
                                                                                                       r ->
                                                                                                        r) ])))
                                                                                          [ (\l
                                                                                              r ->
                                                                                               r) ]))))
                                                                            , (forced
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
                                                                                                     (forced
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
                                                                                                          (forced
                                                                                                             "Unlock not permitted until vestingPeriodEnd time"
                                                                                                             (constr 0
                                                                                                                [  ]))) ]) ])
                                                                                             (unBData
                                                                                                (forced
                                                                                                   (case
                                                                                                      (unConstrData
                                                                                                         (forced
                                                                                                            (case
                                                                                                               (unConstrData
                                                                                                                  (forced
                                                                                                                     vdFields))
                                                                                                               [ (\l
                                                                                                                   r ->
                                                                                                                    r) ])))
                                                                                                      [ (\l
                                                                                                          r ->
                                                                                                           r) ]))))
                                                                                          (unIData
                                                                                             (forced
                                                                                                (forced
                                                                                                   (forced
                                                                                                      (forced
                                                                                                         (forced
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
                                                                                                           (forced
                                                                                                              "Time range not Finite"
                                                                                                              (constr 0
                                                                                                                 [  ])))
                                                                                                      , (addInteger
                                                                                                           (unIData
                                                                                                              (forced
                                                                                                                 extFields))
                                                                                                           offset) ])
                                                                                                   (case
                                                                                                      (equalsInteger
                                                                                                         1
                                                                                                         (case
                                                                                                            (unConstrData
                                                                                                               (forced
                                                                                                                  (forced
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
                                                                                             (forced
                                                                                                lowerFields)))
                                                                                       (case
                                                                                          (unConstrData
                                                                                             (forced
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
                                                                        (forced
                                                                           "Validation failed"
                                                                           (constr 0
                                                                              [  ])))
                                                                   , (forced
                                                                        "Validation completed"
                                                                        ()) ])
                                                                (case
                                                                   spendingInfo
                                                                   [ (\l r ->
                                                                        r) ]))
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
                                                                           (forced
                                                                              "Not spending script"
                                                                              (constr 0
                                                                                 [  ])))
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
                                                                                            (forced
                                                                                               "Missing datum"
                                                                                               (constr 0
                                                                                                  [  ])))
                                                                                       , (mkPairData
                                                                                            ownRef
                                                                                            (forced
                                                                                               mdFields)) ])
                                                                                    (forced
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
                                                                              (forced
                                                                                 (forced
                                                                                    fields)))) ])
                                                                   (case
                                                                      con
                                                                      [ (\l
                                                                          r ->
                                                                           r) ]))
                                                                (case
                                                                   con
                                                                   [ (\l r ->
                                                                        l) ]))
                                                             (unConstrData
                                                                (forced
                                                                   (forced
                                                                      (forced
                                                                         ctxFields))))))
                                                       (case
                                                          (unConstrData
                                                             (forced
                                                                (forced
                                                                   ctxFields)))
                                                          [(\l r -> l)]))
                                                    (unListData
                                                       (forced txInfoFields)))
                                                 (unListData
                                                    (forced txInfoFields)))
                                              (forced txInfoFields))
                                           (unListData
                                              (forced (forced txInfoFields))))
                                        (forced
                                           (forced
                                              (forced
                                                 (forced
                                                    (forced txInfoFields))))))
                                     (forced (forced txInfoFields)))
                                  (case
                                     (unConstrData (forced ctxFields))
                                     [(\l r -> r)]))
                               (case
                                  (unConstrData
                                     (forced
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
                                         (forced
                                            "Own output not found"
                                            (constr 0 [])))
                                    , (\out outs ->
                                         case
                                           (equalsData
                                              (forced
                                                 (case
                                                    (unConstrData out)
                                                    [(\l r -> r)]))
                                              addr)
                                           [ (findOutputByAddress addr outs)
                                           , out ])
                                    , outputs ])
                                 [caseList'])))
                      (fix1
                         (\findInputByOutRef ref inputs ->
                            case
                              (constr 0
                                 [ ((\x -> error)
                                      (forced
                                         "Own input not found"
                                         (constr 0 [])))
                                 , (\txIn txIns ->
                                      case
                                        (equalsData
                                           (forced
                                              (case
                                                 (unConstrData txIn)
                                                 [(\l r -> r)]))
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
                                                   (unBData (forced credFields))
                                                   scriptHash)
                                                [rest, (addInteger 1 rest)]) ])
                                        (case credCon [(\l r -> r)]))
                                     (case credCon [(\l r -> l)]))
                                  (unConstrData
                                     (forced
                                        (case
                                           (unConstrData
                                              (forced
                                                 (case
                                                    (unConstrData
                                                       (forced
                                                          (forced
                                                             (case
                                                                (unConstrData
                                                                   txIn)
                                                                [ (\l r ->
                                                                     r) ]))))
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
                                                                               s
                                                                                 s
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
                               x)
                          x))
                  (\s -> f (\x -> s s x)))) ]
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