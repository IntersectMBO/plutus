(program
  (let
    (nonrec)
    (datatypebind
      (datatype
        (tyvardecl Tuple2 (fun (type) (fun (type) (type))))
        (tyvardecl a (type)) (tyvardecl b (type))
        Tuple2_match
        (vardecl Tuple2 (fun a (fun b [[Tuple2 a] b])))
      )
    )
    (let
      (rec)
      (datatypebind
        (datatype
          (tyvardecl List (fun (type) (type)))
          (tyvardecl a (type))
          Nil_match
          (vardecl Nil [List a]) (vardecl Cons (fun a (fun [List a] [List a])))
        )
      )
      (let
        (nonrec)
        (datatypebind
          (datatype
            (tyvardecl Bool (type))

            Bool_match
            (vardecl True Bool) (vardecl False Bool)
          )
        )
        (datatypebind
          (datatype
            (tyvardecl These (fun (type) (fun (type) (type))))
            (tyvardecl a (type)) (tyvardecl b (type))
            These_match
            (vardecl That (fun b [[These a] b]))
            (vardecl These (fun a (fun b [[These a] b])))
            (vardecl This (fun a [[These a] b]))
          )
        )
        (termbind
          (strict)
          (vardecl
            fToDataByteString_ctoBuiltinData (fun (con bytestring) (con data))
          )
          (lam b (con bytestring) [ (builtin bData) b ])
        )
        (termbind
          (strict)
          (vardecl fToDataInteger_ctoBuiltinData (fun (con integer) (con data)))
          (lam i (con integer) [ (builtin iData) i ])
        )
        (termbind
          (strict)
          (vardecl
            fToDataTuple2_ctoBuiltinData
            (all a (type) (all b (type) (fun [(lam a (type) (fun a (con data))) a] (fun [(lam a (type) (fun a (con data))) b] (fun [[Tuple2 a] b] (con data))))))
          )
          (abs
            a
            (type)
            (abs
              b
              (type)
              (lam
                dToData
                [(lam a (type) (fun a (con data))) a]
                (lam
                  dToData
                  [(lam a (type) (fun a (con data))) b]
                  (lam
                    ds
                    [[Tuple2 a] b]
                    [
                      { [ { { Tuple2_match a } b } ds ] (con data) }
                      (lam
                        arg
                        a
                        (lam
                          arg
                          b
                          [
                            [ (builtin constrData) (con integer 0) ]
                            [
                              [
                                { (builtin mkCons) (con data) } [ dToData arg ]
                              ]
                              [
                                [
                                  { (builtin mkCons) (con data) }
                                  [ dToData arg ]
                                ]
                                [ (builtin mkNilData) (con unit ()) ]
                              ]
                            ]
                          ]
                        )
                      )
                    ]
                  )
                )
              )
            )
          )
        )
        (termbind
          (nonstrict)
          (vardecl fToDataMap [(con list) (con data)])
          [ (builtin mkNilData) (con unit ()) ]
        )
        (termbind
          (strict)
          (vardecl
            fToDataMap_ctoBuiltinData
            (all k (type) (all v (type) (fun [(lam a (type) (fun a (con data))) k] (fun [(lam a (type) (fun a (con data))) v] (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) k] v] (con data))))))
          )
          (abs
            k
            (type)
            (abs
              v
              (type)
              (lam
                dToData
                [(lam a (type) (fun a (con data))) k]
                (lam
                  dToData
                  [(lam a (type) (fun a (con data))) v]
                  (lam
                    eta
                    [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) k] v]
                    (let
                      (rec)
                      (termbind
                        (strict)
                        (vardecl
                          go (fun [List [[Tuple2 k] v]] [(con list) (con data)])
                        )
                        (lam
                          ds
                          [List [[Tuple2 k] v]]
                          (force
                            [
                              [
                                {
                                  [ { Nil_match [[Tuple2 k] v] } ds ]
                                  (delayed [(con list) (con data)])
                                }
                                (delay fToDataMap)
                              ]
                              (lam
                                x
                                [[Tuple2 k] v]
                                (lam
                                  xs
                                  [List [[Tuple2 k] v]]
                                  (delay
                                    [
                                      [
                                        { (builtin mkCons) (con data) }
                                        [
                                          [
                                            [
                                              {
                                                {
                                                  fToDataTuple2_ctoBuiltinData k
                                                }
                                                v
                                              }
                                              dToData
                                            ]
                                            dToData
                                          ]
                                          x
                                        ]
                                      ]
                                      [ go xs ]
                                    ]
                                  )
                                )
                              )
                            ]
                          )
                        )
                      )
                      [ (builtin listData) [ go eta ] ]
                    )
                  )
                )
              )
            )
          )
        )
        (termbind
          (nonstrict)
          (vardecl
            fToDataValue
            (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)] (con data))
          )
          [
            [
              { { fToDataMap_ctoBuiltinData (con bytestring) } (con integer) }
              fToDataByteString_ctoBuiltinData
            ]
            fToDataInteger_ctoBuiltinData
          ]
        )
        (datatypebind
          (datatype
            (tyvardecl Payment (type))

            Payment_match
            (vardecl
              Payment
              (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun (con bytestring) (fun (con integer) Payment)))
            )
          )
        )
        (termbind
          (strict)
          (vardecl fToDataInput_ctoBuiltinData (fun Payment (con data)))
          (lam
            ds
            Payment
            [
              { [ Payment_match ds ] (con data) }
              (lam
                arg
                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                (lam
                  arg
                  (con bytestring)
                  (lam
                    arg
                    (con integer)
                    [
                      [ (builtin constrData) (con integer 0) ]
                      [
                        [
                          { (builtin mkCons) (con data) }
                          [
                            [
                              [
                                {
                                  { fToDataMap_ctoBuiltinData (con bytestring) }
                                  [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]
                                }
                                fToDataByteString_ctoBuiltinData
                              ]
                              fToDataValue
                            ]
                            arg
                          ]
                        ]
                        [
                          [
                            { (builtin mkCons) (con data) }
                            [ (builtin bData) arg ]
                          ]
                          [
                            [
                              { (builtin mkCons) (con data) }
                              [ (builtin iData) arg ]
                            ]
                            [ (builtin mkNilData) (con unit ()) ]
                          ]
                        ]
                      ]
                    ]
                  )
                )
              )
            ]
          )
        )
        (datatypebind
          (datatype
            (tyvardecl MSState (type))

            MSState_match
            (vardecl
              CollectingSignatures
              (fun Payment (fun [List (con bytestring)] MSState))
            )
            (vardecl Holding MSState)
          )
        )
        (termbind
          (strict)
          (vardecl fToDataMSState_ctoBuiltinData (fun MSState (con data)))
          (lam
            ds
            MSState
            (force
              [
                [
                  { [ MSState_match ds ] (delayed (con data)) }
                  (lam
                    arg
                    Payment
                    (lam
                      arg
                      [List (con bytestring)]
                      (let
                        (rec)
                        (termbind
                          (strict)
                          (vardecl
                            go
                            (fun [List (con bytestring)] [(con list) (con data)])
                          )
                          (lam
                            ds
                            [List (con bytestring)]
                            (force
                              [
                                [
                                  {
                                    [ { Nil_match (con bytestring) } ds ]
                                    (delayed [(con list) (con data)])
                                  }
                                  (delay [ (builtin mkNilData) (con unit ()) ])
                                ]
                                (lam
                                  x
                                  (con bytestring)
                                  (lam
                                    xs
                                    [List (con bytestring)]
                                    (delay
                                      [
                                        [
                                          { (builtin mkCons) (con data) }
                                          [ (builtin bData) x ]
                                        ]
                                        [ go xs ]
                                      ]
                                    )
                                  )
                                )
                              ]
                            )
                          )
                        )
                        (delay
                          [
                            [ (builtin constrData) (con integer 1) ]
                            [
                              [
                                { (builtin mkCons) (con data) }
                                [ fToDataInput_ctoBuiltinData arg ]
                              ]
                              [
                                [
                                  { (builtin mkCons) (con data) }
                                  [ (builtin listData) [ go arg ] ]
                                ]
                                [ (builtin mkNilData) (con unit ()) ]
                              ]
                            ]
                          ]
                        )
                      )
                    )
                  )
                ]
                (delay
                  [
                    [ (builtin constrData) (con integer 0) ]
                    [ (builtin mkNilData) (con unit ()) ]
                  ]
                )
              ]
            )
          )
        )
        (datatypebind
          (datatype
            (tyvardecl Credential (type))

            Credential_match
            (vardecl PubKeyCredential (fun (con bytestring) Credential))
            (vardecl ScriptCredential (fun (con bytestring) Credential))
          )
        )
        (datatypebind
          (datatype
            (tyvardecl StakingCredential (type))

            StakingCredential_match
            (vardecl StakingHash (fun Credential StakingCredential))
            (vardecl
              StakingPtr
              (fun (con integer) (fun (con integer) (fun (con integer) StakingCredential)))
            )
          )
        )
        (datatypebind
          (datatype
            (tyvardecl DCert (type))

            DCert_match
            (vardecl DCertDelegDeRegKey (fun StakingCredential DCert))
            (vardecl
              DCertDelegDelegate
              (fun StakingCredential (fun (con bytestring) DCert))
            )
            (vardecl DCertDelegRegKey (fun StakingCredential DCert))
            (vardecl DCertGenesis DCert)
            (vardecl DCertMir DCert)
            (vardecl
              DCertPoolRegister
              (fun (con bytestring) (fun (con bytestring) DCert))
            )
            (vardecl
              DCertPoolRetire (fun (con bytestring) (fun (con integer) DCert))
            )
          )
        )
        (datatypebind
          (datatype
            (tyvardecl TxOutRef (type))

            TxOutRef_match
            (vardecl
              TxOutRef (fun (con bytestring) (fun (con integer) TxOutRef))
            )
          )
        )
        (datatypebind
          (datatype
            (tyvardecl ScriptPurpose (type))

            ScriptPurpose_match
            (vardecl Certifying (fun DCert ScriptPurpose))
            (vardecl Minting (fun (con bytestring) ScriptPurpose))
            (vardecl Rewarding (fun StakingCredential ScriptPurpose))
            (vardecl Spending (fun TxOutRef ScriptPurpose))
          )
        )
        (datatypebind
          (datatype
            (tyvardecl Extended (fun (type) (type)))
            (tyvardecl a (type))
            Extended_match
            (vardecl Finite (fun a [Extended a]))
            (vardecl NegInf [Extended a])
            (vardecl PosInf [Extended a])
          )
        )
        (datatypebind
          (datatype
            (tyvardecl LowerBound (fun (type) (type)))
            (tyvardecl a (type))
            LowerBound_match
            (vardecl LowerBound (fun [Extended a] (fun Bool [LowerBound a])))
          )
        )
        (datatypebind
          (datatype
            (tyvardecl UpperBound (fun (type) (type)))
            (tyvardecl a (type))
            UpperBound_match
            (vardecl UpperBound (fun [Extended a] (fun Bool [UpperBound a])))
          )
        )
        (datatypebind
          (datatype
            (tyvardecl Interval (fun (type) (type)))
            (tyvardecl a (type))
            Interval_match
            (vardecl
              Interval (fun [LowerBound a] (fun [UpperBound a] [Interval a]))
            )
          )
        )
        (datatypebind
          (datatype
            (tyvardecl Maybe (fun (type) (type)))
            (tyvardecl a (type))
            Maybe_match
            (vardecl Just (fun a [Maybe a])) (vardecl Nothing [Maybe a])
          )
        )
        (datatypebind
          (datatype
            (tyvardecl Address (type))

            Address_match
            (vardecl
              Address (fun Credential (fun [Maybe StakingCredential] Address))
            )
          )
        )
        (datatypebind
          (datatype
            (tyvardecl TxOut (type))

            TxOut_match
            (vardecl
              TxOut
              (fun Address (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun [Maybe (con bytestring)] TxOut)))
            )
          )
        )
        (datatypebind
          (datatype
            (tyvardecl TxInInfo (type))

            TxInInfo_match
            (vardecl TxInInfo (fun TxOutRef (fun TxOut TxInInfo)))
          )
        )
        (datatypebind
          (datatype
            (tyvardecl TxInfo (type))

            TxInfo_match
            (vardecl
              TxInfo
              (fun [List TxInInfo] (fun [List TxOut] (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun [List DCert] (fun [List [[Tuple2 StakingCredential] (con integer)]] (fun [Interval (con integer)] (fun [List (con bytestring)] (fun [List [[Tuple2 (con bytestring)] (con data)]] (fun (con bytestring) TxInfo))))))))))
            )
          )
        )
        (datatypebind
          (datatype
            (tyvardecl ScriptContext (type))

            ScriptContext_match
            (vardecl
              ScriptContext (fun TxInfo (fun ScriptPurpose ScriptContext))
            )
          )
        )
        (termbind
          (strict)
          (vardecl
            mkStateMachine
            (all s (type) (all i (type) (fun s (fun i (fun ScriptContext Bool)))))
          )
          (abs
            s
            (type)
            (abs i (type) (lam ds s (lam ds i (lam ds ScriptContext True))))
          )
        )
        (datatypebind
          (datatype
            (tyvardecl ThreadToken (type))

            ThreadToken_match
            (vardecl
              ThreadToken (fun TxOutRef (fun (con bytestring) ThreadToken))
            )
          )
        )
        (datatypebind
          (datatype
            (tyvardecl State (fun (type) (type)))
            (tyvardecl s (type))
            State_match
            (vardecl
              State
              (fun s (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] [State s]))
            )
          )
        )
        (datatypebind (datatype (tyvardecl Void (type))  Void_match ))
        (datatypebind
          (datatype
            (tyvardecl InputConstraint (fun (type) (type)))
            (tyvardecl a (type))
            InputConstraint_match
            (vardecl InputConstraint (fun a (fun TxOutRef [InputConstraint a])))
          )
        )
        (datatypebind
          (datatype
            (tyvardecl OutputConstraint (fun (type) (type)))
            (tyvardecl a (type))
            OutputConstraint_match
            (vardecl
              OutputConstraint
              (fun a (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] [OutputConstraint a]))
            )
          )
        )
        (datatypebind
          (datatype
            (tyvardecl TxConstraint (type))

            TxConstraint_match
            (vardecl MustBeSignedBy (fun (con bytestring) TxConstraint))
            (vardecl
              MustHashDatum (fun (con bytestring) (fun (con data) TxConstraint))
            )
            (vardecl MustIncludeDatum (fun (con data) TxConstraint))
            (vardecl
              MustMintValue
              (fun (con bytestring) (fun (con data) (fun (con bytestring) (fun (con integer) TxConstraint))))
            )
            (vardecl
              MustPayToOtherScript
              (fun (con bytestring) (fun (con data) (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] TxConstraint)))
            )
            (vardecl
              MustPayToPubKey
              (fun (con bytestring) (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] TxConstraint))
            )
            (vardecl
              MustProduceAtLeast
              (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] TxConstraint)
            )
            (vardecl
              MustSpendAtLeast
              (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] TxConstraint)
            )
            (vardecl MustSpendPubKeyOutput (fun TxOutRef TxConstraint))
            (vardecl
              MustSpendScriptOutput (fun TxOutRef (fun (con data) TxConstraint))
            )
            (vardecl MustValidateIn (fun [Interval (con integer)] TxConstraint))
          )
        )
        (datatypebind
          (datatype
            (tyvardecl TxConstraints (fun (type) (fun (type) (type))))
            (tyvardecl i (type)) (tyvardecl o (type))
            TxConstraints_match
            (vardecl
              TxConstraints
              (fun [List TxConstraint] (fun [List [InputConstraint i]] (fun [List [OutputConstraint o]] [[TxConstraints i] o])))
            )
          )
        )
        (datatypebind
          (datatype
            (tyvardecl StateMachine (fun (type) (fun (type) (type))))
            (tyvardecl s (type)) (tyvardecl i (type))
            StateMachine_match
            (vardecl
              StateMachine
              (fun (fun [State s] (fun i [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State s]]])) (fun (fun s Bool) (fun (fun s (fun i (fun ScriptContext Bool))) (fun [Maybe ThreadToken] [[StateMachine s] i]))))
            )
          )
        )
        (termbind
          (strict)
          (vardecl
            fAdditiveGroupValue_cscale
            (fun (con integer) (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]))
          )
          (lam
            i
            (con integer)
            (lam
              ds
              [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
              (let
                (rec)
                (termbind
                  (strict)
                  (vardecl
                    go
                    (fun [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]] [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]])
                  )
                  (lam
                    ds
                    [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                    (force
                      [
                        [
                          {
                            [
                              {
                                Nil_match
                                [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                              }
                              ds
                            ]
                            (delayed [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]])
                          }
                          (delay
                            {
                              Nil
                              [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                            }
                          )
                        ]
                        (lam
                          ds
                          [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                          (lam
                            xs
                            [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                            (delay
                              [
                                {
                                  [
                                    {
                                      { Tuple2_match (con bytestring) }
                                      [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]
                                    }
                                    ds
                                  ]
                                  [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                }
                                (lam
                                  c
                                  (con bytestring)
                                  (lam
                                    i
                                    [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]
                                    (let
                                      (rec)
                                      (termbind
                                        (strict)
                                        (vardecl
                                          go
                                          (fun [List [[Tuple2 (con bytestring)] (con integer)]] [List [[Tuple2 (con bytestring)] (con integer)]])
                                        )
                                        (lam
                                          ds
                                          [List [[Tuple2 (con bytestring)] (con integer)]]
                                          (force
                                            [
                                              [
                                                {
                                                  [
                                                    {
                                                      Nil_match
                                                      [[Tuple2 (con bytestring)] (con integer)]
                                                    }
                                                    ds
                                                  ]
                                                  (delayed [List [[Tuple2 (con bytestring)] (con integer)]])
                                                }
                                                (delay
                                                  {
                                                    Nil
                                                    [[Tuple2 (con bytestring)] (con integer)]
                                                  }
                                                )
                                              ]
                                              (lam
                                                ds
                                                [[Tuple2 (con bytestring)] (con integer)]
                                                (lam
                                                  xs
                                                  [List [[Tuple2 (con bytestring)] (con integer)]]
                                                  (delay
                                                    [
                                                      {
                                                        [
                                                          {
                                                            {
                                                              Tuple2_match
                                                              (con bytestring)
                                                            }
                                                            (con integer)
                                                          }
                                                          ds
                                                        ]
                                                        [List [[Tuple2 (con bytestring)] (con integer)]]
                                                      }
                                                      (lam
                                                        c
                                                        (con bytestring)
                                                        (lam
                                                          i
                                                          (con integer)
                                                          [
                                                            [
                                                              {
                                                                Cons
                                                                [[Tuple2 (con bytestring)] (con integer)]
                                                              }
                                                              [
                                                                [
                                                                  {
                                                                    {
                                                                      Tuple2
                                                                      (con bytestring)
                                                                    }
                                                                    (con integer)
                                                                  }
                                                                  c
                                                                ]
                                                                [
                                                                  [
                                                                    (builtin
                                                                      multiplyInteger
                                                                    )
                                                                    i
                                                                  ]
                                                                  i
                                                                ]
                                                              ]
                                                            ]
                                                            [ go xs ]
                                                          ]
                                                        )
                                                      )
                                                    ]
                                                  )
                                                )
                                              )
                                            ]
                                          )
                                        )
                                      )
                                      [
                                        [
                                          {
                                            Cons
                                            [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                          }
                                          [
                                            [
                                              {
                                                { Tuple2 (con bytestring) }
                                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]
                                              }
                                              c
                                            ]
                                            [ go i ]
                                          ]
                                        ]
                                        [ go xs ]
                                      ]
                                    )
                                  )
                                )
                              ]
                            )
                          )
                        )
                      ]
                    )
                  )
                )
                [ go ds ]
              )
            )
          )
        )
        (termbind
          (strict)
          (vardecl
            addInteger (fun (con integer) (fun (con integer) (con integer)))
          )
          (lam
            x
            (con integer)
            (lam y (con integer) [ [ (builtin addInteger) x ] y ])
          )
        )
        (termbind
          (strict)
          (vardecl
            equalsByteString (fun (con bytestring) (fun (con bytestring) Bool))
          )
          (lam
            x
            (con bytestring)
            (lam
              y
              (con bytestring)
              [
                [
                  [
                    { (builtin ifThenElse) Bool }
                    [ [ (builtin equalsByteString) x ] y ]
                  ]
                  True
                ]
                False
              ]
            )
          )
        )
        (datatypebind
          (datatype
            (tyvardecl AdditiveMonoid (fun (type) (type)))
            (tyvardecl a (type))
            AdditiveMonoid_match
            (vardecl
              CConsAdditiveMonoid
              (fun [(lam a (type) (fun a (fun a a))) a] (fun a [AdditiveMonoid a]))
            )
          )
        )
        (termbind
          (strict)
          (vardecl bad_name (fun Bool (fun Bool Bool)))
          (lam
            ds
            Bool
            (lam
              ds
              Bool
              (force
                [
                  [ { [ Bool_match ds ] (delayed Bool) } (delay True) ]
                  (delay ds)
                ]
              )
            )
          )
        )
        (termbind
          (nonstrict)
          (vardecl fAdditiveMonoidBool [AdditiveMonoid Bool])
          [ [ { CConsAdditiveMonoid Bool } bad_name ] False ]
        )
        (datatypebind
          (datatype
            (tyvardecl Monoid (fun (type) (type)))
            (tyvardecl a (type))
            Monoid_match
            (vardecl
              CConsMonoid
              (fun [(lam a (type) (fun a (fun a a))) a] (fun a [Monoid a]))
            )
          )
        )
        (termbind
          (strict)
          (vardecl
            p1Monoid
            (all a (type) (fun [Monoid a] [(lam a (type) (fun a (fun a a))) a]))
          )
          (abs
            a
            (type)
            (lam
              v
              [Monoid a]
              [
                {
                  [ { Monoid_match a } v ] [(lam a (type) (fun a (fun a a))) a]
                }
                (lam v [(lam a (type) (fun a (fun a a))) a] (lam v a v))
              ]
            )
          )
        )
        (termbind
          (strict)
          (vardecl mempty (all a (type) (fun [Monoid a] a)))
          (abs
            a
            (type)
            (lam
              v
              [Monoid a]
              [
                { [ { Monoid_match a } v ] a }
                (lam v [(lam a (type) (fun a (fun a a))) a] (lam v a v))
              ]
            )
          )
        )
        (let
          (rec)
          (termbind
            (strict)
            (vardecl
              fFoldableNil_cfoldMap
              (all m (type) (all a (type) (fun [Monoid m] (fun (fun a m) (fun [List a] m)))))
            )
            (abs
              m
              (type)
              (abs
                a
                (type)
                (lam
                  dMonoid
                  [Monoid m]
                  (let
                    (nonrec)
                    (termbind
                      (nonstrict)
                      (vardecl dSemigroup [(lam a (type) (fun a (fun a a))) m])
                      [ { p1Monoid m } dMonoid ]
                    )
                    (lam
                      ds
                      (fun a m)
                      (lam
                        ds
                        [List a]
                        (force
                          [
                            [
                              { [ { Nil_match a } ds ] (delayed m) }
                              (delay [ { mempty m } dMonoid ])
                            ]
                            (lam
                              x
                              a
                              (lam
                                xs
                                [List a]
                                (delay
                                  [
                                    [ dSemigroup [ ds x ] ]
                                    [
                                      [
                                        [
                                          { { fFoldableNil_cfoldMap m } a }
                                          dMonoid
                                        ]
                                        ds
                                      ]
                                      xs
                                    ]
                                  ]
                                )
                              )
                            )
                          ]
                        )
                      )
                    )
                  )
                )
              )
            )
          )
          (let
            (rec)
            (termbind
              (strict)
              (vardecl
                fFunctorNil_cfmap
                (all a (type) (all b (type) (fun (fun a b) (fun [List a] [List b]))))
              )
              (abs
                a
                (type)
                (abs
                  b
                  (type)
                  (lam
                    f
                    (fun a b)
                    (lam
                      l
                      [List a]
                      (force
                        [
                          [
                            { [ { Nil_match a } l ] (delayed [List b]) }
                            (delay { Nil b })
                          ]
                          (lam
                            x
                            a
                            (lam
                              xs
                              [List a]
                              (delay
                                [
                                  [ { Cons b } [ f x ] ]
                                  [ [ { { fFunctorNil_cfmap a } b } f ] xs ]
                                ]
                              )
                            )
                          )
                        ]
                      )
                    )
                  )
                )
              )
            )
            (let
              (nonrec)
              (termbind
                (strict)
                (vardecl
                  p1AdditiveMonoid
                  (all a (type) (fun [AdditiveMonoid a] [(lam a (type) (fun a (fun a a))) a]))
                )
                (abs
                  a
                  (type)
                  (lam
                    v
                    [AdditiveMonoid a]
                    [
                      {
                        [ { AdditiveMonoid_match a } v ]
                        [(lam a (type) (fun a (fun a a))) a]
                      }
                      (lam v [(lam a (type) (fun a (fun a a))) a] (lam v a v))
                    ]
                  )
                )
              )
              (termbind
                (strict)
                (vardecl zero (all a (type) (fun [AdditiveMonoid a] a)))
                (abs
                  a
                  (type)
                  (lam
                    v
                    [AdditiveMonoid a]
                    [
                      { [ { AdditiveMonoid_match a } v ] a }
                      (lam v [(lam a (type) (fun a (fun a a))) a] (lam v a v))
                    ]
                  )
                )
              )
              (termbind
                (strict)
                (vardecl
                  fMonoidSum
                  (all a (type) (fun [AdditiveMonoid a] [Monoid [(lam a (type) a) a]]))
                )
                (abs
                  a
                  (type)
                  (lam
                    v
                    [AdditiveMonoid a]
                    [
                      [
                        { CConsMonoid [(lam a (type) a) a] }
                        (lam
                          eta
                          [(lam a (type) a) a]
                          (lam
                            eta
                            [(lam a (type) a) a]
                            [ [ [ { p1AdditiveMonoid a } v ] eta ] eta ]
                          )
                        )
                      ]
                      [ { zero a } v ]
                    ]
                  )
                )
              )
              (let
                (rec)
                (termbind
                  (strict)
                  (vardecl
                    foldr
                    (all a (type) (all b (type) (fun (fun a (fun b b)) (fun b (fun [List a] b)))))
                  )
                  (abs
                    a
                    (type)
                    (abs
                      b
                      (type)
                      (lam
                        f
                        (fun a (fun b b))
                        (lam
                          acc
                          b
                          (lam
                            l
                            [List a]
                            (force
                              [
                                [
                                  { [ { Nil_match a } l ] (delayed b) }
                                  (delay acc)
                                ]
                                (lam
                                  x
                                  a
                                  (lam
                                    xs
                                    [List a]
                                    (delay
                                      [
                                        [ f x ]
                                        [ [ [ { { foldr a } b } f ] acc ] xs ]
                                      ]
                                    )
                                  )
                                )
                              ]
                            )
                          )
                        )
                      )
                    )
                  )
                )
                (let
                  (nonrec)
                  (termbind
                    (strict)
                    (vardecl
                      union
                      (all k (type) (all v (type) (all r (type) (fun [(lam a (type) (fun a (fun a Bool))) k] (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) k] v] (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) k] r] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) k] [[These v] r]]))))))
                    )
                    (abs
                      k
                      (type)
                      (abs
                        v
                        (type)
                        (abs
                          r
                          (type)
                          (lam
                            dEq
                            [(lam a (type) (fun a (fun a Bool))) k]
                            (lam
                              ds
                              [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) k] v]
                              (lam
                                ds
                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) k] r]
                                [
                                  [
                                    [
                                      {
                                        { foldr [[Tuple2 k] [[These v] r]] }
                                        [List [[Tuple2 k] [[These v] r]]]
                                      }
                                      { Cons [[Tuple2 k] [[These v] r]] }
                                    ]
                                    [
                                      [
                                        {
                                          { fFunctorNil_cfmap [[Tuple2 k] r] }
                                          [[Tuple2 k] [[These v] r]]
                                        }
                                        (lam
                                          ds
                                          [[Tuple2 k] r]
                                          [
                                            {
                                              [ { { Tuple2_match k } r } ds ]
                                              [[Tuple2 k] [[These v] r]]
                                            }
                                            (lam
                                              c
                                              k
                                              (lam
                                                b
                                                r
                                                [
                                                  [
                                                    {
                                                      { Tuple2 k } [[These v] r]
                                                    }
                                                    c
                                                  ]
                                                  [ { { That v } r } b ]
                                                ]
                                              )
                                            )
                                          ]
                                        )
                                      ]
                                      [
                                        [
                                          [
                                            {
                                              { foldr [[Tuple2 k] r] }
                                              [List [[Tuple2 k] r]]
                                            }
                                            (lam
                                              e
                                              [[Tuple2 k] r]
                                              (lam
                                                xs
                                                [List [[Tuple2 k] r]]
                                                [
                                                  {
                                                    [
                                                      { { Tuple2_match k } r } e
                                                    ]
                                                    [List [[Tuple2 k] r]]
                                                  }
                                                  (lam
                                                    c
                                                    k
                                                    (lam
                                                      ds
                                                      r
                                                      (force
                                                        [
                                                          [
                                                            {
                                                              [
                                                                Bool_match
                                                                [
                                                                  [
                                                                    [
                                                                      {
                                                                        {
                                                                          fFoldableNil_cfoldMap
                                                                          [(lam a (type) a) Bool]
                                                                        }
                                                                        [[Tuple2 k] v]
                                                                      }
                                                                      [
                                                                        {
                                                                          fMonoidSum
                                                                          Bool
                                                                        }
                                                                        fAdditiveMonoidBool
                                                                      ]
                                                                    ]
                                                                    (lam
                                                                      ds
                                                                      [[Tuple2 k] v]
                                                                      [
                                                                        {
                                                                          [
                                                                            {
                                                                              {
                                                                                Tuple2_match
                                                                                k
                                                                              }
                                                                              v
                                                                            }
                                                                            ds
                                                                          ]
                                                                          Bool
                                                                        }
                                                                        (lam
                                                                          c
                                                                          k
                                                                          (lam
                                                                            ds
                                                                            v
                                                                            [
                                                                              [
                                                                                dEq
                                                                                c
                                                                              ]
                                                                              c
                                                                            ]
                                                                          )
                                                                        )
                                                                      ]
                                                                    )
                                                                  ]
                                                                  ds
                                                                ]
                                                              ]
                                                              (delayed [List [[Tuple2 k] r]])
                                                            }
                                                            (delay xs)
                                                          ]
                                                          (delay
                                                            [
                                                              [
                                                                {
                                                                  Cons
                                                                  [[Tuple2 k] r]
                                                                }
                                                                e
                                                              ]
                                                              xs
                                                            ]
                                                          )
                                                        ]
                                                      )
                                                    )
                                                  )
                                                ]
                                              )
                                            )
                                          ]
                                          { Nil [[Tuple2 k] r] }
                                        ]
                                        ds
                                      ]
                                    ]
                                  ]
                                  [
                                    [
                                      {
                                        { fFunctorNil_cfmap [[Tuple2 k] v] }
                                        [[Tuple2 k] [[These v] r]]
                                      }
                                      (lam
                                        ds
                                        [[Tuple2 k] v]
                                        [
                                          {
                                            [ { { Tuple2_match k } v } ds ]
                                            [[Tuple2 k] [[These v] r]]
                                          }
                                          (lam
                                            c
                                            k
                                            (lam
                                              i
                                              v
                                              (let
                                                (rec)
                                                (termbind
                                                  (strict)
                                                  (vardecl
                                                    go
                                                    (fun [List [[Tuple2 k] r]] [[These v] r])
                                                  )
                                                  (lam
                                                    ds
                                                    [List [[Tuple2 k] r]]
                                                    (force
                                                      [
                                                        [
                                                          {
                                                            [
                                                              {
                                                                Nil_match
                                                                [[Tuple2 k] r]
                                                              }
                                                              ds
                                                            ]
                                                            (delayed [[These v] r])
                                                          }
                                                          (delay
                                                            [
                                                              { { This v } r } i
                                                            ]
                                                          )
                                                        ]
                                                        (lam
                                                          ds
                                                          [[Tuple2 k] r]
                                                          (lam
                                                            xs
                                                            [List [[Tuple2 k] r]]
                                                            (delay
                                                              [
                                                                {
                                                                  [
                                                                    {
                                                                      {
                                                                        Tuple2_match
                                                                        k
                                                                      }
                                                                      r
                                                                    }
                                                                    ds
                                                                  ]
                                                                  [[These v] r]
                                                                }
                                                                (lam
                                                                  c
                                                                  k
                                                                  (lam
                                                                    i
                                                                    r
                                                                    (force
                                                                      [
                                                                        [
                                                                          {
                                                                            [
                                                                              Bool_match
                                                                              [
                                                                                [
                                                                                  dEq
                                                                                  c
                                                                                ]
                                                                                c
                                                                              ]
                                                                            ]
                                                                            (delayed [[These v] r])
                                                                          }
                                                                          (delay
                                                                            [
                                                                              [
                                                                                {
                                                                                  {
                                                                                    These
                                                                                    v
                                                                                  }
                                                                                  r
                                                                                }
                                                                                i
                                                                              ]
                                                                              i
                                                                            ]
                                                                          )
                                                                        ]
                                                                        (delay
                                                                          [
                                                                            go
                                                                            xs
                                                                          ]
                                                                        )
                                                                      ]
                                                                    )
                                                                  )
                                                                )
                                                              ]
                                                            )
                                                          )
                                                        )
                                                      ]
                                                    )
                                                  )
                                                )
                                                [
                                                  [
                                                    {
                                                      { Tuple2 k } [[These v] r]
                                                    }
                                                    c
                                                  ]
                                                  [ go ds ]
                                                ]
                                              )
                                            )
                                          )
                                        ]
                                      )
                                    ]
                                    ds
                                  ]
                                ]
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      unionVal
                      (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]]))
                    )
                    (lam
                      ds
                      [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                      (lam
                        ds
                        [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                        (let
                          (rec)
                          (termbind
                            (strict)
                            (vardecl
                              go
                              (fun [List [[Tuple2 (con bytestring)] [[These [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]] [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]]])
                            )
                            (lam
                              ds
                              [List [[Tuple2 (con bytestring)] [[These [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]]
                              (force
                                [
                                  [
                                    {
                                      [
                                        {
                                          Nil_match
                                          [[Tuple2 (con bytestring)] [[These [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                        }
                                        ds
                                      ]
                                      (delayed [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]]])
                                    }
                                    (delay
                                      {
                                        Nil
                                        [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]]
                                      }
                                    )
                                  ]
                                  (lam
                                    ds
                                    [[Tuple2 (con bytestring)] [[These [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                    (lam
                                      xs
                                      [List [[Tuple2 (con bytestring)] [[These [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]]
                                      (delay
                                        [
                                          {
                                            [
                                              {
                                                {
                                                  Tuple2_match (con bytestring)
                                                }
                                                [[These [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                              }
                                              ds
                                            ]
                                            [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]]]
                                          }
                                          (lam
                                            c
                                            (con bytestring)
                                            (lam
                                              i
                                              [[These [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                              [
                                                [
                                                  {
                                                    Cons
                                                    [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]]
                                                  }
                                                  [
                                                    [
                                                      {
                                                        {
                                                          Tuple2
                                                          (con bytestring)
                                                        }
                                                        [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]
                                                      }
                                                      c
                                                    ]
                                                    [
                                                      [
                                                        [
                                                          {
                                                            [
                                                              {
                                                                {
                                                                  These_match
                                                                  [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]
                                                                }
                                                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]
                                                              }
                                                              i
                                                            ]
                                                            [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]
                                                          }
                                                          (lam
                                                            b
                                                            [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]
                                                            (let
                                                              (rec)
                                                              (termbind
                                                                (strict)
                                                                (vardecl
                                                                  go
                                                                  (fun [List [[Tuple2 (con bytestring)] (con integer)]] [List [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]])
                                                                )
                                                                (lam
                                                                  ds
                                                                  [List [[Tuple2 (con bytestring)] (con integer)]]
                                                                  (force
                                                                    [
                                                                      [
                                                                        {
                                                                          [
                                                                            {
                                                                              Nil_match
                                                                              [[Tuple2 (con bytestring)] (con integer)]
                                                                            }
                                                                            ds
                                                                          ]
                                                                          (delayed [List [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]])
                                                                        }
                                                                        (delay
                                                                          {
                                                                            Nil
                                                                            [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]
                                                                          }
                                                                        )
                                                                      ]
                                                                      (lam
                                                                        ds
                                                                        [[Tuple2 (con bytestring)] (con integer)]
                                                                        (lam
                                                                          xs
                                                                          [List [[Tuple2 (con bytestring)] (con integer)]]
                                                                          (delay
                                                                            [
                                                                              {
                                                                                [
                                                                                  {
                                                                                    {
                                                                                      Tuple2_match
                                                                                      (con bytestring)
                                                                                    }
                                                                                    (con integer)
                                                                                  }
                                                                                  ds
                                                                                ]
                                                                                [List [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]]
                                                                              }
                                                                              (lam
                                                                                c
                                                                                (con bytestring)
                                                                                (lam
                                                                                  i
                                                                                  (con integer)
                                                                                  [
                                                                                    [
                                                                                      {
                                                                                        Cons
                                                                                        [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]
                                                                                      }
                                                                                      [
                                                                                        [
                                                                                          {
                                                                                            {
                                                                                              Tuple2
                                                                                              (con bytestring)
                                                                                            }
                                                                                            [[These (con integer)] (con integer)]
                                                                                          }
                                                                                          c
                                                                                        ]
                                                                                        [
                                                                                          {
                                                                                            {
                                                                                              That
                                                                                              (con integer)
                                                                                            }
                                                                                            (con integer)
                                                                                          }
                                                                                          i
                                                                                        ]
                                                                                      ]
                                                                                    ]
                                                                                    [
                                                                                      go
                                                                                      xs
                                                                                    ]
                                                                                  ]
                                                                                )
                                                                              )
                                                                            ]
                                                                          )
                                                                        )
                                                                      )
                                                                    ]
                                                                  )
                                                                )
                                                              )
                                                              [ go b ]
                                                            )
                                                          )
                                                        ]
                                                        (lam
                                                          a
                                                          [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]
                                                          (lam
                                                            b
                                                            [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]
                                                            [
                                                              [
                                                                [
                                                                  {
                                                                    {
                                                                      {
                                                                        union
                                                                        (con bytestring)
                                                                      }
                                                                      (con integer)
                                                                    }
                                                                    (con integer)
                                                                  }
                                                                  equalsByteString
                                                                ]
                                                                a
                                                              ]
                                                              b
                                                            ]
                                                          )
                                                        )
                                                      ]
                                                      (lam
                                                        a
                                                        [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]
                                                        (let
                                                          (rec)
                                                          (termbind
                                                            (strict)
                                                            (vardecl
                                                              go
                                                              (fun [List [[Tuple2 (con bytestring)] (con integer)]] [List [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]])
                                                            )
                                                            (lam
                                                              ds
                                                              [List [[Tuple2 (con bytestring)] (con integer)]]
                                                              (force
                                                                [
                                                                  [
                                                                    {
                                                                      [
                                                                        {
                                                                          Nil_match
                                                                          [[Tuple2 (con bytestring)] (con integer)]
                                                                        }
                                                                        ds
                                                                      ]
                                                                      (delayed [List [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]])
                                                                    }
                                                                    (delay
                                                                      {
                                                                        Nil
                                                                        [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]
                                                                      }
                                                                    )
                                                                  ]
                                                                  (lam
                                                                    ds
                                                                    [[Tuple2 (con bytestring)] (con integer)]
                                                                    (lam
                                                                      xs
                                                                      [List [[Tuple2 (con bytestring)] (con integer)]]
                                                                      (delay
                                                                        [
                                                                          {
                                                                            [
                                                                              {
                                                                                {
                                                                                  Tuple2_match
                                                                                  (con bytestring)
                                                                                }
                                                                                (con integer)
                                                                              }
                                                                              ds
                                                                            ]
                                                                            [List [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]]
                                                                          }
                                                                          (lam
                                                                            c
                                                                            (con bytestring)
                                                                            (lam
                                                                              i
                                                                              (con integer)
                                                                              [
                                                                                [
                                                                                  {
                                                                                    Cons
                                                                                    [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]
                                                                                  }
                                                                                  [
                                                                                    [
                                                                                      {
                                                                                        {
                                                                                          Tuple2
                                                                                          (con bytestring)
                                                                                        }
                                                                                        [[These (con integer)] (con integer)]
                                                                                      }
                                                                                      c
                                                                                    ]
                                                                                    [
                                                                                      {
                                                                                        {
                                                                                          This
                                                                                          (con integer)
                                                                                        }
                                                                                        (con integer)
                                                                                      }
                                                                                      i
                                                                                    ]
                                                                                  ]
                                                                                ]
                                                                                [
                                                                                  go
                                                                                  xs
                                                                                ]
                                                                              ]
                                                                            )
                                                                          )
                                                                        ]
                                                                      )
                                                                    )
                                                                  )
                                                                ]
                                                              )
                                                            )
                                                          )
                                                          [ go a ]
                                                        )
                                                      )
                                                    ]
                                                  ]
                                                ]
                                                [ go xs ]
                                              ]
                                            )
                                          )
                                        ]
                                      )
                                    )
                                  )
                                ]
                              )
                            )
                          )
                          [
                            go
                            [
                              [
                                [
                                  {
                                    {
                                      { union (con bytestring) }
                                      [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]
                                    }
                                    [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]
                                  }
                                  equalsByteString
                                ]
                                ds
                              ]
                              ds
                            ]
                          ]
                        )
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      unionWith
                      (fun (fun (con integer) (fun (con integer) (con integer))) (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]])))
                    )
                    (lam
                      f
                      (fun (con integer) (fun (con integer) (con integer)))
                      (lam
                        ls
                        [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                        (lam
                          rs
                          [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                          (let
                            (rec)
                            (termbind
                              (strict)
                              (vardecl
                                go
                                (fun [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]]] [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]])
                              )
                              (lam
                                ds
                                [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]]]
                                (force
                                  [
                                    [
                                      {
                                        [
                                          {
                                            Nil_match
                                            [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]]
                                          }
                                          ds
                                        ]
                                        (delayed [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]])
                                      }
                                      (delay
                                        {
                                          Nil
                                          [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                        }
                                      )
                                    ]
                                    (lam
                                      ds
                                      [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]]
                                      (lam
                                        xs
                                        [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]]]
                                        (delay
                                          [
                                            {
                                              [
                                                {
                                                  {
                                                    Tuple2_match
                                                    (con bytestring)
                                                  }
                                                  [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]
                                                }
                                                ds
                                              ]
                                              [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                            }
                                            (lam
                                              c
                                              (con bytestring)
                                              (lam
                                                i
                                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]
                                                (let
                                                  (rec)
                                                  (termbind
                                                    (strict)
                                                    (vardecl
                                                      go
                                                      (fun [List [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]] [List [[Tuple2 (con bytestring)] (con integer)]])
                                                    )
                                                    (lam
                                                      ds
                                                      [List [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]]
                                                      (force
                                                        [
                                                          [
                                                            {
                                                              [
                                                                {
                                                                  Nil_match
                                                                  [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]
                                                                }
                                                                ds
                                                              ]
                                                              (delayed [List [[Tuple2 (con bytestring)] (con integer)]])
                                                            }
                                                            (delay
                                                              {
                                                                Nil
                                                                [[Tuple2 (con bytestring)] (con integer)]
                                                              }
                                                            )
                                                          ]
                                                          (lam
                                                            ds
                                                            [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]
                                                            (lam
                                                              xs
                                                              [List [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]]
                                                              (delay
                                                                [
                                                                  {
                                                                    [
                                                                      {
                                                                        {
                                                                          Tuple2_match
                                                                          (con bytestring)
                                                                        }
                                                                        [[These (con integer)] (con integer)]
                                                                      }
                                                                      ds
                                                                    ]
                                                                    [List [[Tuple2 (con bytestring)] (con integer)]]
                                                                  }
                                                                  (lam
                                                                    c
                                                                    (con bytestring)
                                                                    (lam
                                                                      i
                                                                      [[These (con integer)] (con integer)]
                                                                      [
                                                                        [
                                                                          {
                                                                            Cons
                                                                            [[Tuple2 (con bytestring)] (con integer)]
                                                                          }
                                                                          [
                                                                            [
                                                                              {
                                                                                {
                                                                                  Tuple2
                                                                                  (con bytestring)
                                                                                }
                                                                                (con integer)
                                                                              }
                                                                              c
                                                                            ]
                                                                            [
                                                                              [
                                                                                [
                                                                                  {
                                                                                    [
                                                                                      {
                                                                                        {
                                                                                          These_match
                                                                                          (con integer)
                                                                                        }
                                                                                        (con integer)
                                                                                      }
                                                                                      i
                                                                                    ]
                                                                                    (con integer)
                                                                                  }
                                                                                  (lam
                                                                                    b
                                                                                    (con integer)
                                                                                    [
                                                                                      [
                                                                                        f
                                                                                        (con
                                                                                          integer
                                                                                            0
                                                                                        )
                                                                                      ]
                                                                                      b
                                                                                    ]
                                                                                  )
                                                                                ]
                                                                                (lam
                                                                                  a
                                                                                  (con integer)
                                                                                  (lam
                                                                                    b
                                                                                    (con integer)
                                                                                    [
                                                                                      [
                                                                                        f
                                                                                        a
                                                                                      ]
                                                                                      b
                                                                                    ]
                                                                                  )
                                                                                )
                                                                              ]
                                                                              (lam
                                                                                a
                                                                                (con integer)
                                                                                [
                                                                                  [
                                                                                    f
                                                                                    a
                                                                                  ]
                                                                                  (con
                                                                                    integer
                                                                                      0
                                                                                  )
                                                                                ]
                                                                              )
                                                                            ]
                                                                          ]
                                                                        ]
                                                                        [
                                                                          go xs
                                                                        ]
                                                                      ]
                                                                    )
                                                                  )
                                                                ]
                                                              )
                                                            )
                                                          )
                                                        ]
                                                      )
                                                    )
                                                  )
                                                  [
                                                    [
                                                      {
                                                        Cons
                                                        [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                      }
                                                      [
                                                        [
                                                          {
                                                            {
                                                              Tuple2
                                                              (con bytestring)
                                                            }
                                                            [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]
                                                          }
                                                          c
                                                        ]
                                                        [ go i ]
                                                      ]
                                                    ]
                                                    [ go xs ]
                                                  ]
                                                )
                                              )
                                            )
                                          ]
                                        )
                                      )
                                    )
                                  ]
                                )
                              )
                            )
                            [ go [ [ unionVal ls ] rs ] ]
                          )
                        )
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      fAdditiveGroupValue
                      (fun [(lam a (type) a) [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]] (fun [(lam a (type) a) [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]))
                    )
                    (lam
                      ds
                      [(lam a (type) a) [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                      (lam
                        ds
                        [(lam a (type) a) [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                        [
                          [ [ unionWith addInteger ] ds ]
                          [ [ fAdditiveGroupValue_cscale (con integer -1) ] ds ]
                        ]
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      fMonoidTxConstraints_cmempty
                      (all i (type) (all o (type) [[TxConstraints i] o]))
                    )
                    (abs
                      i
                      (type)
                      (abs
                        o
                        (type)
                        [
                          [
                            [ { { TxConstraints i } o } { Nil TxConstraint } ]
                            { Nil [InputConstraint i] }
                          ]
                          { Nil [OutputConstraint o] }
                        ]
                      )
                    )
                  )
                  (datatypebind
                    (datatype
                      (tyvardecl Input (type))

                      Input_match
                      (vardecl AddSignature (fun (con bytestring) Input))
                      (vardecl Cancel Input)
                      (vardecl Pay Input)
                      (vardecl ProposePayment (fun Payment Input))
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      checkBinRel
                      (fun (fun (con integer) (fun (con integer) Bool)) (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] Bool)))
                    )
                    (lam
                      f
                      (fun (con integer) (fun (con integer) Bool))
                      (lam
                        l
                        [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                        (lam
                          r
                          [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                          (let
                            (rec)
                            (termbind
                              (strict)
                              (vardecl
                                go
                                (fun [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]]] Bool)
                              )
                              (lam
                                xs
                                [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]]]
                                (force
                                  [
                                    [
                                      {
                                        [
                                          {
                                            Nil_match
                                            [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]]
                                          }
                                          xs
                                        ]
                                        (delayed Bool)
                                      }
                                      (delay True)
                                    ]
                                    (lam
                                      ds
                                      [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]]
                                      (lam
                                        xs
                                        [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]]]
                                        (delay
                                          [
                                            {
                                              [
                                                {
                                                  {
                                                    Tuple2_match
                                                    (con bytestring)
                                                  }
                                                  [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]
                                                }
                                                ds
                                              ]
                                              Bool
                                            }
                                            (lam
                                              ds
                                              (con bytestring)
                                              (lam
                                                x
                                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]
                                                (let
                                                  (rec)
                                                  (termbind
                                                    (strict)
                                                    (vardecl
                                                      go
                                                      (fun [List [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]] Bool)
                                                    )
                                                    (lam
                                                      xs
                                                      [List [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]]
                                                      (force
                                                        [
                                                          [
                                                            {
                                                              [
                                                                {
                                                                  Nil_match
                                                                  [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]
                                                                }
                                                                xs
                                                              ]
                                                              (delayed Bool)
                                                            }
                                                            (delay [ go xs ])
                                                          ]
                                                          (lam
                                                            ds
                                                            [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]
                                                            (lam
                                                              xs
                                                              [List [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]]
                                                              (delay
                                                                [
                                                                  {
                                                                    [
                                                                      {
                                                                        {
                                                                          Tuple2_match
                                                                          (con bytestring)
                                                                        }
                                                                        [[These (con integer)] (con integer)]
                                                                      }
                                                                      ds
                                                                    ]
                                                                    Bool
                                                                  }
                                                                  (lam
                                                                    ds
                                                                    (con bytestring)
                                                                    (lam
                                                                      x
                                                                      [[These (con integer)] (con integer)]
                                                                      [
                                                                        [
                                                                          [
                                                                            {
                                                                              [
                                                                                {
                                                                                  {
                                                                                    These_match
                                                                                    (con integer)
                                                                                  }
                                                                                  (con integer)
                                                                                }
                                                                                x
                                                                              ]
                                                                              Bool
                                                                            }
                                                                            (lam
                                                                              b
                                                                              (con integer)
                                                                              (force
                                                                                [
                                                                                  [
                                                                                    {
                                                                                      [
                                                                                        Bool_match
                                                                                        [
                                                                                          [
                                                                                            f
                                                                                            (con
                                                                                              integer
                                                                                                0
                                                                                            )
                                                                                          ]
                                                                                          b
                                                                                        ]
                                                                                      ]
                                                                                      (delayed Bool)
                                                                                    }
                                                                                    (delay
                                                                                      [
                                                                                        go
                                                                                        xs
                                                                                      ]
                                                                                    )
                                                                                  ]
                                                                                  (delay
                                                                                    False
                                                                                  )
                                                                                ]
                                                                              )
                                                                            )
                                                                          ]
                                                                          (lam
                                                                            a
                                                                            (con integer)
                                                                            (lam
                                                                              b
                                                                              (con integer)
                                                                              (force
                                                                                [
                                                                                  [
                                                                                    {
                                                                                      [
                                                                                        Bool_match
                                                                                        [
                                                                                          [
                                                                                            f
                                                                                            a
                                                                                          ]
                                                                                          b
                                                                                        ]
                                                                                      ]
                                                                                      (delayed Bool)
                                                                                    }
                                                                                    (delay
                                                                                      [
                                                                                        go
                                                                                        xs
                                                                                      ]
                                                                                    )
                                                                                  ]
                                                                                  (delay
                                                                                    False
                                                                                  )
                                                                                ]
                                                                              )
                                                                            )
                                                                          )
                                                                        ]
                                                                        (lam
                                                                          a
                                                                          (con integer)
                                                                          (force
                                                                            [
                                                                              [
                                                                                {
                                                                                  [
                                                                                    Bool_match
                                                                                    [
                                                                                      [
                                                                                        f
                                                                                        a
                                                                                      ]
                                                                                      (con
                                                                                        integer
                                                                                          0
                                                                                      )
                                                                                    ]
                                                                                  ]
                                                                                  (delayed Bool)
                                                                                }
                                                                                (delay
                                                                                  [
                                                                                    go
                                                                                    xs
                                                                                  ]
                                                                                )
                                                                              ]
                                                                              (delay
                                                                                False
                                                                              )
                                                                            ]
                                                                          )
                                                                        )
                                                                      ]
                                                                    )
                                                                  )
                                                                ]
                                                              )
                                                            )
                                                          )
                                                        ]
                                                      )
                                                    )
                                                  )
                                                  [ go x ]
                                                )
                                              )
                                            )
                                          ]
                                        )
                                      )
                                    )
                                  ]
                                )
                              )
                            )
                            [ go [ [ unionVal l ] r ] ]
                          )
                        )
                      )
                    )
                  )
                  (datatypebind
                    (datatype
                      (tyvardecl Params (type))

                      Params_match
                      (vardecl
                        Params
                        (fun [List (con bytestring)] (fun (con integer) Params))
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      isSignatory (fun (con bytestring) (fun Params Bool))
                    )
                    (lam
                      pkh
                      (con bytestring)
                      (lam
                        ds
                        Params
                        [
                          { [ Params_match ds ] Bool }
                          (lam
                            sigs
                            [List (con bytestring)]
                            (lam
                              ds
                              (con integer)
                              [
                                [
                                  [
                                    {
                                      {
                                        fFoldableNil_cfoldMap
                                        [(lam a (type) a) Bool]
                                      }
                                      (con bytestring)
                                    }
                                    [ { fMonoidSum Bool } fAdditiveMonoidBool ]
                                  ]
                                  (lam
                                    pkh
                                    (con bytestring)
                                    [ [ equalsByteString pkh ] pkh ]
                                  )
                                ]
                                sigs
                              ]
                            )
                          )
                        ]
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      lessThanEqInteger
                      (fun (con integer) (fun (con integer) Bool))
                    )
                    (lam
                      x
                      (con integer)
                      (lam
                        y
                        (con integer)
                        [
                          [
                            [
                              { (builtin ifThenElse) Bool }
                              [ [ (builtin lessThanEqualsInteger) x ] y ]
                            ]
                            True
                          ]
                          False
                        ]
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      build
                      (all a (type) (fun (all b (type) (fun (fun a (fun b b)) (fun b b))) [List a]))
                    )
                    (abs
                      a
                      (type)
                      (lam
                        g
                        (all b (type) (fun (fun a (fun b b)) (fun b b)))
                        [ [ { g [List a] } { Cons a } ] { Nil a } ]
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      mustBeSignedBy
                      (all i (type) (all o (type) (fun (con bytestring) [[TxConstraints i] o])))
                    )
                    (abs
                      i
                      (type)
                      (abs
                        o
                        (type)
                        (lam
                          x
                          (con bytestring)
                          [
                            [
                              [
                                { { TxConstraints i } o }
                                [
                                  { build TxConstraint }
                                  (abs
                                    a
                                    (type)
                                    (lam
                                      c
                                      (fun TxConstraint (fun a a))
                                      (lam n a [ [ c [ MustBeSignedBy x ] ] n ])
                                    )
                                  )
                                ]
                              ]
                              { Nil [InputConstraint i] }
                            ]
                            { Nil [OutputConstraint o] }
                          ]
                        )
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      fMonoidDual
                      (all a (type) (fun [Monoid a] [Monoid [(lam a (type) a) a]]))
                    )
                    (abs
                      a
                      (type)
                      (lam
                        v
                        [Monoid a]
                        [
                          [
                            { CConsMonoid [(lam a (type) a) a] }
                            (lam
                              eta
                              [(lam a (type) a) a]
                              (lam
                                eta
                                [(lam a (type) a) a]
                                [ [ [ { p1Monoid a } v ] eta ] eta ]
                              )
                            )
                          ]
                          [ { mempty a } v ]
                        ]
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      bad_name
                      (all b (type) (all c (type) (all a (type) (fun (fun b c) (fun (fun a b) (fun a c))))))
                    )
                    (abs
                      b
                      (type)
                      (abs
                        c
                        (type)
                        (abs
                          a
                          (type)
                          (lam
                            f
                            (fun b c)
                            (lam g (fun a b) (lam x a [ f [ g x ] ]))
                          )
                        )
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      fSemigroupEndo_c
                      (all a (type) (fun [(lam a (type) (fun a a)) a] (fun [(lam a (type) (fun a a)) a] [(lam a (type) (fun a a)) a])))
                    )
                    (abs
                      a
                      (type)
                      (lam
                        ds
                        [(lam a (type) (fun a a)) a]
                        (lam
                          ds
                          [(lam a (type) (fun a a)) a]
                          [ [ { { { bad_name a } a } a } ds ] ds ]
                        )
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl id (all a (type) (fun a a)))
                    (abs a (type) (lam x a x))
                  )
                  (termbind
                    (strict)
                    (vardecl
                      fMonoidEndo
                      (all a (type) [Monoid [(lam a (type) (fun a a)) a]])
                    )
                    (abs
                      a
                      (type)
                      [
                        [
                          { CConsMonoid [(lam a (type) (fun a a)) a] }
                          { fSemigroupEndo_c a }
                        ]
                        { id a }
                      ]
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      length
                      (all t (fun (type) (type)) (all a (type) (fun [(lam t (fun (type) (type)) (all m (type) (all a (type) (fun [Monoid m] (fun (fun a m) (fun [t a] m)))))) t] (fun [t a] (con integer)))))
                    )
                    (abs
                      t
                      (fun (type) (type))
                      (abs
                        a
                        (type)
                        (lam
                          dFoldable
                          [(lam t (fun (type) (type)) (all m (type) (all a (type) (fun [Monoid m] (fun (fun a m) (fun [t a] m)))))) t]
                          (let
                            (nonrec)
                            (termbind
                              (nonstrict)
                              (vardecl
                                dMonoid
                                [Monoid [(lam a (type) a) [(lam a (type) (fun a a)) (con integer)]]]
                              )
                              [
                                {
                                  fMonoidDual
                                  [(lam a (type) (fun a a)) (con integer)]
                                }
                                { fMonoidEndo (con integer) }
                              ]
                            )
                            (lam
                              t
                              [t a]
                              [
                                [
                                  [
                                    [
                                      {
                                        {
                                          dFoldable
                                          [(lam a (type) a) [(lam a (type) (fun a a)) (con integer)]]
                                        }
                                        a
                                      }
                                      dMonoid
                                    ]
                                    (lam
                                      x
                                      a
                                      (lam
                                        y
                                        (con integer)
                                        [
                                          [ (builtin addInteger) y ]
                                          (con integer 1)
                                        ]
                                      )
                                    )
                                  ]
                                  t
                                ]
                                (con integer 0)
                              ]
                            )
                          )
                        )
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      proposalAccepted
                      (fun Params (fun [List (con bytestring)] Bool))
                    )
                    (lam
                      ds
                      Params
                      (lam
                        pks
                        [List (con bytestring)]
                        [
                          { [ Params_match ds ] Bool }
                          (lam
                            signatories
                            [List (con bytestring)]
                            (lam
                              numReq
                              (con integer)
                              [
                                [
                                  [
                                    { (builtin ifThenElse) Bool }
                                    [
                                      [
                                        (builtin greaterThanEqualsInteger)
                                        [
                                          [
                                            { { length List } (con bytestring) }
                                            fFoldableNil_cfoldMap
                                          ]
                                          [
                                            [
                                              [
                                                {
                                                  { foldr (con bytestring) }
                                                  [List (con bytestring)]
                                                }
                                                (lam
                                                  e
                                                  (con bytestring)
                                                  (lam
                                                    xs
                                                    [List (con bytestring)]
                                                    (force
                                                      [
                                                        [
                                                          {
                                                            [
                                                              Bool_match
                                                              [
                                                                [
                                                                  [
                                                                    {
                                                                      {
                                                                        fFoldableNil_cfoldMap
                                                                        [(lam a (type) a) Bool]
                                                                      }
                                                                      (con bytestring)
                                                                    }
                                                                    [
                                                                      {
                                                                        fMonoidSum
                                                                        Bool
                                                                      }
                                                                      fAdditiveMonoidBool
                                                                    ]
                                                                  ]
                                                                  (lam
                                                                    pk
                                                                    (con bytestring)
                                                                    [
                                                                      [
                                                                        equalsByteString
                                                                        pk
                                                                      ]
                                                                      e
                                                                    ]
                                                                  )
                                                                ]
                                                                pks
                                                              ]
                                                            ]
                                                            (delayed [List (con bytestring)])
                                                          }
                                                          (delay
                                                            [
                                                              [
                                                                {
                                                                  Cons
                                                                  (con bytestring)
                                                                }
                                                                e
                                                              ]
                                                              xs
                                                            ]
                                                          )
                                                        ]
                                                        (delay xs)
                                                      ]
                                                    )
                                                  )
                                                )
                                              ]
                                              { Nil (con bytestring) }
                                            ]
                                            signatories
                                          ]
                                        ]
                                      ]
                                      numReq
                                    ]
                                  ]
                                  True
                                ]
                                False
                              ]
                            )
                          )
                        ]
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      transition
                      (fun Params (fun [State MSState] (fun Input [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State MSState]]])))
                    )
                    (lam
                      params
                      Params
                      (lam
                        ds
                        [State MSState]
                        (lam
                          i
                          Input
                          [
                            {
                              [ { State_match MSState } ds ]
                              [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State MSState]]]
                            }
                            (lam
                              ds
                              MSState
                              (lam
                                ds
                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                (force
                                  [
                                    [
                                      {
                                        [ MSState_match ds ]
                                        (delayed [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State MSState]]])
                                      }
                                      (lam
                                        pmt
                                        Payment
                                        (lam
                                          pks
                                          [List (con bytestring)]
                                          (let
                                            (nonrec)
                                            (termbind
                                              (nonstrict)
                                              (vardecl
                                                paymentAmount
                                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                              )
                                              [
                                                {
                                                  [ Payment_match pmt ]
                                                  [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                }
                                                (lam
                                                  ds
                                                  [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                  (lam
                                                    ds
                                                    (con bytestring)
                                                    (lam ds (con integer) ds)
                                                  )
                                                )
                                              ]
                                            )
                                            (delay
                                              (force
                                                [
                                                  [
                                                    [
                                                      [
                                                        {
                                                          [ Input_match i ]
                                                          (delayed [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State MSState]]])
                                                        }
                                                        (lam
                                                          pk
                                                          (con bytestring)
                                                          (delay
                                                            (force
                                                              [
                                                                [
                                                                  {
                                                                    [
                                                                      Bool_match
                                                                      [
                                                                        [
                                                                          isSignatory
                                                                          pk
                                                                        ]
                                                                        params
                                                                      ]
                                                                    ]
                                                                    (delayed [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State MSState]]])
                                                                  }
                                                                  (delay
                                                                    (force
                                                                      [
                                                                        [
                                                                          {
                                                                            [
                                                                              Bool_match
                                                                              [
                                                                                [
                                                                                  [
                                                                                    {
                                                                                      {
                                                                                        fFoldableNil_cfoldMap
                                                                                        [(lam a (type) a) Bool]
                                                                                      }
                                                                                      (con bytestring)
                                                                                    }
                                                                                    [
                                                                                      {
                                                                                        fMonoidSum
                                                                                        Bool
                                                                                      }
                                                                                      fAdditiveMonoidBool
                                                                                    ]
                                                                                  ]
                                                                                  (lam
                                                                                    pk
                                                                                    (con bytestring)
                                                                                    [
                                                                                      [
                                                                                        equalsByteString
                                                                                        pk
                                                                                      ]
                                                                                      pk
                                                                                    ]
                                                                                  )
                                                                                ]
                                                                                pks
                                                                              ]
                                                                            ]
                                                                            (delayed [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State MSState]]])
                                                                          }
                                                                          (delay
                                                                            {
                                                                              Nothing
                                                                              [[Tuple2 [[TxConstraints Void] Void]] [State MSState]]
                                                                            }
                                                                          )
                                                                        ]
                                                                        (delay
                                                                          [
                                                                            {
                                                                              Just
                                                                              [[Tuple2 [[TxConstraints Void] Void]] [State MSState]]
                                                                            }
                                                                            [
                                                                              [
                                                                                {
                                                                                  {
                                                                                    Tuple2
                                                                                    [[TxConstraints Void] Void]
                                                                                  }
                                                                                  [State MSState]
                                                                                }
                                                                                [
                                                                                  {
                                                                                    {
                                                                                      mustBeSignedBy
                                                                                      Void
                                                                                    }
                                                                                    Void
                                                                                  }
                                                                                  pk
                                                                                ]
                                                                              ]
                                                                              [
                                                                                [
                                                                                  {
                                                                                    State
                                                                                    MSState
                                                                                  }
                                                                                  [
                                                                                    [
                                                                                      CollectingSignatures
                                                                                      pmt
                                                                                    ]
                                                                                    [
                                                                                      [
                                                                                        {
                                                                                          Cons
                                                                                          (con bytestring)
                                                                                        }
                                                                                        pk
                                                                                      ]
                                                                                      pks
                                                                                    ]
                                                                                  ]
                                                                                ]
                                                                                ds
                                                                              ]
                                                                            ]
                                                                          ]
                                                                        )
                                                                      ]
                                                                    )
                                                                  )
                                                                ]
                                                                (delay
                                                                  {
                                                                    Nothing
                                                                    [[Tuple2 [[TxConstraints Void] Void]] [State MSState]]
                                                                  }
                                                                )
                                                              ]
                                                            )
                                                          )
                                                        )
                                                      ]
                                                      (delay
                                                        [
                                                          {
                                                            Just
                                                            [[Tuple2 [[TxConstraints Void] Void]] [State MSState]]
                                                          }
                                                          [
                                                            [
                                                              {
                                                                {
                                                                  Tuple2
                                                                  [[TxConstraints Void] Void]
                                                                }
                                                                [State MSState]
                                                              }
                                                              [
                                                                [
                                                                  [
                                                                    {
                                                                      {
                                                                        TxConstraints
                                                                        Void
                                                                      }
                                                                      Void
                                                                    }
                                                                    [
                                                                      {
                                                                        build
                                                                        TxConstraint
                                                                      }
                                                                      (abs
                                                                        a
                                                                        (type)
                                                                        (lam
                                                                          c
                                                                          (fun TxConstraint (fun a a))
                                                                          (lam
                                                                            n
                                                                            a
                                                                            [
                                                                              [
                                                                                c
                                                                                [
                                                                                  MustValidateIn
                                                                                  [
                                                                                    [
                                                                                      {
                                                                                        Interval
                                                                                        (con integer)
                                                                                      }
                                                                                      [
                                                                                        [
                                                                                          {
                                                                                            LowerBound
                                                                                            (con integer)
                                                                                          }
                                                                                          [
                                                                                            {
                                                                                              Finite
                                                                                              (con integer)
                                                                                            }
                                                                                            [
                                                                                              {
                                                                                                [
                                                                                                  Payment_match
                                                                                                  pmt
                                                                                                ]
                                                                                                (con integer)
                                                                                              }
                                                                                              (lam
                                                                                                ds
                                                                                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                (lam
                                                                                                  ds
                                                                                                  (con bytestring)
                                                                                                  (lam
                                                                                                    ds
                                                                                                    (con integer)
                                                                                                    ds
                                                                                                  )
                                                                                                )
                                                                                              )
                                                                                            ]
                                                                                          ]
                                                                                        ]
                                                                                        True
                                                                                      ]
                                                                                    ]
                                                                                    [
                                                                                      [
                                                                                        {
                                                                                          UpperBound
                                                                                          (con integer)
                                                                                        }
                                                                                        {
                                                                                          PosInf
                                                                                          (con integer)
                                                                                        }
                                                                                      ]
                                                                                      True
                                                                                    ]
                                                                                  ]
                                                                                ]
                                                                              ]
                                                                              n
                                                                            ]
                                                                          )
                                                                        )
                                                                      )
                                                                    ]
                                                                  ]
                                                                  {
                                                                    Nil
                                                                    [InputConstraint Void]
                                                                  }
                                                                ]
                                                                {
                                                                  Nil
                                                                  [OutputConstraint Void]
                                                                }
                                                              ]
                                                            ]
                                                            [
                                                              [
                                                                {
                                                                  State MSState
                                                                }
                                                                Holding
                                                              ]
                                                              ds
                                                            ]
                                                          ]
                                                        ]
                                                      )
                                                    ]
                                                    (delay
                                                      (force
                                                        [
                                                          [
                                                            {
                                                              [
                                                                Bool_match
                                                                [
                                                                  [
                                                                    proposalAccepted
                                                                    params
                                                                  ]
                                                                  pks
                                                                ]
                                                              ]
                                                              (delayed [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State MSState]]])
                                                            }
                                                            (delay
                                                              [
                                                                {
                                                                  Just
                                                                  [[Tuple2 [[TxConstraints Void] Void]] [State MSState]]
                                                                }
                                                                [
                                                                  [
                                                                    {
                                                                      {
                                                                        Tuple2
                                                                        [[TxConstraints Void] Void]
                                                                      }
                                                                      [State MSState]
                                                                    }
                                                                    [
                                                                      [
                                                                        [
                                                                          {
                                                                            {
                                                                              TxConstraints
                                                                              Void
                                                                            }
                                                                            Void
                                                                          }
                                                                          [
                                                                            [
                                                                              [
                                                                                {
                                                                                  {
                                                                                    foldr
                                                                                    TxConstraint
                                                                                  }
                                                                                  [List TxConstraint]
                                                                                }
                                                                                {
                                                                                  Cons
                                                                                  TxConstraint
                                                                                }
                                                                              ]
                                                                              [
                                                                                {
                                                                                  build
                                                                                  TxConstraint
                                                                                }
                                                                                (abs
                                                                                  a
                                                                                  (type)
                                                                                  (lam
                                                                                    c
                                                                                    (fun TxConstraint (fun a a))
                                                                                    (lam
                                                                                      n
                                                                                      a
                                                                                      [
                                                                                        [
                                                                                          c
                                                                                          [
                                                                                            [
                                                                                              MustPayToPubKey
                                                                                              [
                                                                                                {
                                                                                                  [
                                                                                                    Payment_match
                                                                                                    pmt
                                                                                                  ]
                                                                                                  (con bytestring)
                                                                                                }
                                                                                                (lam
                                                                                                  ds
                                                                                                  [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                  (lam
                                                                                                    ds
                                                                                                    (con bytestring)
                                                                                                    (lam
                                                                                                      ds
                                                                                                      (con integer)
                                                                                                      ds
                                                                                                    )
                                                                                                  )
                                                                                                )
                                                                                              ]
                                                                                            ]
                                                                                            paymentAmount
                                                                                          ]
                                                                                        ]
                                                                                        n
                                                                                      ]
                                                                                    )
                                                                                  )
                                                                                )
                                                                              ]
                                                                            ]
                                                                            [
                                                                              {
                                                                                build
                                                                                TxConstraint
                                                                              }
                                                                              (abs
                                                                                a
                                                                                (type)
                                                                                (lam
                                                                                  c
                                                                                  (fun TxConstraint (fun a a))
                                                                                  (lam
                                                                                    n
                                                                                    a
                                                                                    [
                                                                                      [
                                                                                        c
                                                                                        [
                                                                                          MustValidateIn
                                                                                          [
                                                                                            [
                                                                                              {
                                                                                                Interval
                                                                                                (con integer)
                                                                                              }
                                                                                              [
                                                                                                [
                                                                                                  {
                                                                                                    LowerBound
                                                                                                    (con integer)
                                                                                                  }
                                                                                                  {
                                                                                                    NegInf
                                                                                                    (con integer)
                                                                                                  }
                                                                                                ]
                                                                                                True
                                                                                              ]
                                                                                            ]
                                                                                            [
                                                                                              [
                                                                                                {
                                                                                                  UpperBound
                                                                                                  (con integer)
                                                                                                }
                                                                                                [
                                                                                                  {
                                                                                                    Finite
                                                                                                    (con integer)
                                                                                                  }
                                                                                                  [
                                                                                                    [
                                                                                                      (builtin
                                                                                                        subtractInteger
                                                                                                      )
                                                                                                      [
                                                                                                        {
                                                                                                          [
                                                                                                            Payment_match
                                                                                                            pmt
                                                                                                          ]
                                                                                                          (con integer)
                                                                                                        }
                                                                                                        (lam
                                                                                                          ds
                                                                                                          [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                          (lam
                                                                                                            ds
                                                                                                            (con bytestring)
                                                                                                            (lam
                                                                                                              ds
                                                                                                              (con integer)
                                                                                                              ds
                                                                                                            )
                                                                                                          )
                                                                                                        )
                                                                                                      ]
                                                                                                    ]
                                                                                                    (con
                                                                                                      integer
                                                                                                        1
                                                                                                    )
                                                                                                  ]
                                                                                                ]
                                                                                              ]
                                                                                              True
                                                                                            ]
                                                                                          ]
                                                                                        ]
                                                                                      ]
                                                                                      n
                                                                                    ]
                                                                                  )
                                                                                )
                                                                              )
                                                                            ]
                                                                          ]
                                                                        ]
                                                                        [
                                                                          [
                                                                            [
                                                                              {
                                                                                {
                                                                                  foldr
                                                                                  [InputConstraint Void]
                                                                                }
                                                                                [List [InputConstraint Void]]
                                                                              }
                                                                              {
                                                                                Cons
                                                                                [InputConstraint Void]
                                                                              }
                                                                            ]
                                                                            {
                                                                              Nil
                                                                              [InputConstraint Void]
                                                                            }
                                                                          ]
                                                                          {
                                                                            Nil
                                                                            [InputConstraint Void]
                                                                          }
                                                                        ]
                                                                      ]
                                                                      [
                                                                        [
                                                                          [
                                                                            {
                                                                              {
                                                                                foldr
                                                                                [OutputConstraint Void]
                                                                              }
                                                                              [List [OutputConstraint Void]]
                                                                            }
                                                                            {
                                                                              Cons
                                                                              [OutputConstraint Void]
                                                                            }
                                                                          ]
                                                                          {
                                                                            Nil
                                                                            [OutputConstraint Void]
                                                                          }
                                                                        ]
                                                                        {
                                                                          Nil
                                                                          [OutputConstraint Void]
                                                                        }
                                                                      ]
                                                                    ]
                                                                  ]
                                                                  [
                                                                    [
                                                                      {
                                                                        State
                                                                        MSState
                                                                      }
                                                                      Holding
                                                                    ]
                                                                    [
                                                                      [
                                                                        fAdditiveGroupValue
                                                                        ds
                                                                      ]
                                                                      paymentAmount
                                                                    ]
                                                                  ]
                                                                ]
                                                              ]
                                                            )
                                                          ]
                                                          (delay
                                                            {
                                                              Nothing
                                                              [[Tuple2 [[TxConstraints Void] Void]] [State MSState]]
                                                            }
                                                          )
                                                        ]
                                                      )
                                                    )
                                                  ]
                                                  (lam
                                                    ipv
                                                    Payment
                                                    (delay
                                                      {
                                                        Nothing
                                                        [[Tuple2 [[TxConstraints Void] Void]] [State MSState]]
                                                      }
                                                    )
                                                  )
                                                ]
                                              )
                                            )
                                          )
                                        )
                                      )
                                    ]
                                    (delay
                                      (force
                                        [
                                          [
                                            [
                                              [
                                                {
                                                  [ Input_match i ]
                                                  (delayed [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State MSState]]])
                                                }
                                                (lam
                                                  default_arg0
                                                  (con bytestring)
                                                  (delay
                                                    {
                                                      Nothing
                                                      [[Tuple2 [[TxConstraints Void] Void]] [State MSState]]
                                                    }
                                                  )
                                                )
                                              ]
                                              (delay
                                                {
                                                  Nothing
                                                  [[Tuple2 [[TxConstraints Void] Void]] [State MSState]]
                                                }
                                              )
                                            ]
                                            (delay
                                              {
                                                Nothing
                                                [[Tuple2 [[TxConstraints Void] Void]] [State MSState]]
                                              }
                                            )
                                          ]
                                          (lam
                                            pmt
                                            Payment
                                            (delay
                                              [
                                                {
                                                  [ Payment_match pmt ]
                                                  [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State MSState]]]
                                                }
                                                (lam
                                                  amt
                                                  [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                  (lam
                                                    ds
                                                    (con bytestring)
                                                    (lam
                                                      ds
                                                      (con integer)
                                                      (force
                                                        [
                                                          [
                                                            {
                                                              [
                                                                Bool_match
                                                                [
                                                                  [
                                                                    [
                                                                      checkBinRel
                                                                      lessThanEqInteger
                                                                    ]
                                                                    amt
                                                                  ]
                                                                  ds
                                                                ]
                                                              ]
                                                              (delayed [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State MSState]]])
                                                            }
                                                            (delay
                                                              [
                                                                {
                                                                  Just
                                                                  [[Tuple2 [[TxConstraints Void] Void]] [State MSState]]
                                                                }
                                                                [
                                                                  [
                                                                    {
                                                                      {
                                                                        Tuple2
                                                                        [[TxConstraints Void] Void]
                                                                      }
                                                                      [State MSState]
                                                                    }
                                                                    {
                                                                      {
                                                                        fMonoidTxConstraints_cmempty
                                                                        Void
                                                                      }
                                                                      Void
                                                                    }
                                                                  ]
                                                                  [
                                                                    [
                                                                      {
                                                                        State
                                                                        MSState
                                                                      }
                                                                      [
                                                                        [
                                                                          CollectingSignatures
                                                                          pmt
                                                                        ]
                                                                        {
                                                                          Nil
                                                                          (con bytestring)
                                                                        }
                                                                      ]
                                                                    ]
                                                                    ds
                                                                  ]
                                                                ]
                                                              ]
                                                            )
                                                          ]
                                                          (delay
                                                            {
                                                              Nothing
                                                              [[Tuple2 [[TxConstraints Void] Void]] [State MSState]]
                                                            }
                                                          )
                                                        ]
                                                      )
                                                    )
                                                  )
                                                )
                                              ]
                                            )
                                          )
                                        ]
                                      )
                                    )
                                  ]
                                )
                              )
                            )
                          ]
                        )
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl machine (fun Params [[StateMachine MSState] Input])
                    )
                    (lam
                      params
                      Params
                      [
                        [
                          [
                            [
                              { { StateMachine MSState } Input }
                              [ transition params ]
                            ]
                            (lam ds MSState False)
                          ]
                          { { mkStateMachine MSState } Input }
                        ]
                        { Nothing ThreadToken }
                      ]
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl absurd (all a (type) (fun Void a)))
                    (abs a (type) (lam a Void { [ Void_match a ] a }))
                  )
                  (datatypebind
                    (datatype
                      (tyvardecl MultiplicativeMonoid (fun (type) (type)))
                      (tyvardecl a (type))
                      MultiplicativeMonoid_match
                      (vardecl
                        CConsMultiplicativeMonoid
                        (fun [(lam a (type) (fun a (fun a a))) a] (fun a [MultiplicativeMonoid a]))
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      p1MultiplicativeMonoid
                      (all a (type) (fun [MultiplicativeMonoid a] [(lam a (type) (fun a (fun a a))) a]))
                    )
                    (abs
                      a
                      (type)
                      (lam
                        v
                        [MultiplicativeMonoid a]
                        [
                          {
                            [ { MultiplicativeMonoid_match a } v ]
                            [(lam a (type) (fun a (fun a a))) a]
                          }
                          (lam
                            v [(lam a (type) (fun a (fun a a))) a] (lam v a v)
                          )
                        ]
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl one (all a (type) (fun [MultiplicativeMonoid a] a))
                    )
                    (abs
                      a
                      (type)
                      (lam
                        v
                        [MultiplicativeMonoid a]
                        [
                          { [ { MultiplicativeMonoid_match a } v ] a }
                          (lam
                            v [(lam a (type) (fun a (fun a a))) a] (lam v a v)
                          )
                        ]
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      fMonoidProduct
                      (all a (type) (fun [MultiplicativeMonoid a] [Monoid [(lam a (type) a) a]]))
                    )
                    (abs
                      a
                      (type)
                      (lam
                        v
                        [MultiplicativeMonoid a]
                        [
                          [
                            { CConsMonoid [(lam a (type) a) a] }
                            (lam
                              eta
                              [(lam a (type) a) a]
                              (lam
                                eta
                                [(lam a (type) a) a]
                                [
                                  [ [ { p1MultiplicativeMonoid a } v ] eta ] eta
                                ]
                              )
                            )
                          ]
                          [ { one a } v ]
                        ]
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl bad_name (fun Bool (fun Bool Bool)))
                    (lam
                      ds
                      Bool
                      (lam
                        x
                        Bool
                        (force
                          [
                            [ { [ Bool_match ds ] (delayed Bool) } (delay x) ]
                            (delay False)
                          ]
                        )
                      )
                    )
                  )
                  (termbind
                    (nonstrict)
                    (vardecl
                      fMultiplicativeMonoidBool [MultiplicativeMonoid Bool]
                    )
                    [ [ { CConsMultiplicativeMonoid Bool } bad_name ] True ]
                  )
                  (termbind
                    (strict)
                    (vardecl fEqTxOutRef_c (fun TxOutRef (fun TxOutRef Bool)))
                    (lam
                      l
                      TxOutRef
                      (lam
                        r
                        TxOutRef
                        (force
                          [
                            [
                              {
                                [
                                  Bool_match
                                  [
                                    [
                                      [
                                        { (builtin ifThenElse) Bool }
                                        [
                                          [
                                            (builtin equalsByteString)
                                            [
                                              {
                                                [ TxOutRef_match l ]
                                                (con bytestring)
                                              }
                                              (lam
                                                ds
                                                (con bytestring)
                                                (lam ds (con integer) ds)
                                              )
                                            ]
                                          ]
                                          [
                                            {
                                              [ TxOutRef_match r ]
                                              (con bytestring)
                                            }
                                            (lam
                                              ds
                                              (con bytestring)
                                              (lam ds (con integer) ds)
                                            )
                                          ]
                                        ]
                                      ]
                                      True
                                    ]
                                    False
                                  ]
                                ]
                                (delayed Bool)
                              }
                              (delay
                                [
                                  [
                                    [
                                      { (builtin ifThenElse) Bool }
                                      [
                                        [
                                          (builtin equalsInteger)
                                          [
                                            {
                                              [ TxOutRef_match l ] (con integer)
                                            }
                                            (lam
                                              ds
                                              (con bytestring)
                                              (lam ds (con integer) ds)
                                            )
                                          ]
                                        ]
                                        [
                                          { [ TxOutRef_match r ] (con integer) }
                                          (lam
                                            ds
                                            (con bytestring)
                                            (lam ds (con integer) ds)
                                          )
                                        ]
                                      ]
                                    ]
                                    True
                                  ]
                                  False
                                ]
                              )
                            ]
                            (delay False)
                          ]
                        )
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      checkOwnInputConstraint
                      (all a (type) (fun ScriptContext (fun [InputConstraint a] Bool)))
                    )
                    (abs
                      a
                      (type)
                      (lam
                        ds
                        ScriptContext
                        (lam
                          ds
                          [InputConstraint a]
                          [
                            { [ ScriptContext_match ds ] Bool }
                            (lam
                              ds
                              TxInfo
                              (lam
                                ds
                                ScriptPurpose
                                [
                                  { [ { InputConstraint_match a } ds ] Bool }
                                  (lam
                                    ds
                                    a
                                    (lam
                                      ds
                                      TxOutRef
                                      [
                                        { [ TxInfo_match ds ] Bool }
                                        (lam
                                          ds
                                          [List TxInInfo]
                                          (lam
                                            ds
                                            [List TxOut]
                                            (lam
                                              ds
                                              [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                              (lam
                                                ds
                                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                (lam
                                                  ds
                                                  [List DCert]
                                                  (lam
                                                    ds
                                                    [List [[Tuple2 StakingCredential] (con integer)]]
                                                    (lam
                                                      ds
                                                      [Interval (con integer)]
                                                      (lam
                                                        ds
                                                        [List (con bytestring)]
                                                        (lam
                                                          ds
                                                          [List [[Tuple2 (con bytestring)] (con data)]]
                                                          (lam
                                                            ds
                                                            (con bytestring)
                                                            (force
                                                              [
                                                                [
                                                                  {
                                                                    [
                                                                      Bool_match
                                                                      [
                                                                        [
                                                                          [
                                                                            {
                                                                              {
                                                                                fFoldableNil_cfoldMap
                                                                                [(lam a (type) a) Bool]
                                                                              }
                                                                              TxInInfo
                                                                            }
                                                                            [
                                                                              {
                                                                                fMonoidSum
                                                                                Bool
                                                                              }
                                                                              fAdditiveMonoidBool
                                                                            ]
                                                                          ]
                                                                          (lam
                                                                            ds
                                                                            TxInInfo
                                                                            [
                                                                              {
                                                                                [
                                                                                  TxInInfo_match
                                                                                  ds
                                                                                ]
                                                                                Bool
                                                                              }
                                                                              (lam
                                                                                ds
                                                                                TxOutRef
                                                                                (lam
                                                                                  ds
                                                                                  TxOut
                                                                                  [
                                                                                    [
                                                                                      fEqTxOutRef_c
                                                                                      ds
                                                                                    ]
                                                                                    ds
                                                                                  ]
                                                                                )
                                                                              )
                                                                            ]
                                                                          )
                                                                        ]
                                                                        ds
                                                                      ]
                                                                    ]
                                                                    (delayed Bool)
                                                                  }
                                                                  (delay True)
                                                                ]
                                                                (delay
                                                                  [
                                                                    [
                                                                      {
                                                                        (builtin
                                                                          chooseUnit
                                                                        )
                                                                        Bool
                                                                      }
                                                                      [
                                                                        (builtin
                                                                          trace
                                                                        )
                                                                        (con
                                                                          string
                                                                            "Input constraint"
                                                                        )
                                                                      ]
                                                                    ]
                                                                    False
                                                                  ]
                                                                )
                                                              ]
                                                            )
                                                          )
                                                        )
                                                      )
                                                    )
                                                  )
                                                )
                                              )
                                            )
                                          )
                                        )
                                      ]
                                    )
                                  )
                                ]
                              )
                            )
                          ]
                        )
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      fSemigroupFirst_c
                      (all a (type) (fun [(lam a (type) [Maybe a]) a] (fun [(lam a (type) [Maybe a]) a] [(lam a (type) [Maybe a]) a])))
                    )
                    (abs
                      a
                      (type)
                      (lam
                        ds
                        [(lam a (type) [Maybe a]) a]
                        (lam
                          b
                          [(lam a (type) [Maybe a]) a]
                          (force
                            [
                              [
                                {
                                  [ { Maybe_match a } ds ]
                                  (delayed [(lam a (type) [Maybe a]) a])
                                }
                                (lam ipv a (delay ds))
                              ]
                              (delay b)
                            ]
                          )
                        )
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      fMonoidFirst
                      (all a (type) [Monoid [(lam a (type) [Maybe a]) a]])
                    )
                    (abs
                      a
                      (type)
                      [
                        [
                          { CConsMonoid [(lam a (type) [Maybe a]) a] }
                          { fSemigroupFirst_c a }
                        ]
                        { Nothing a }
                      ]
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      findDatumHash
                      (fun (con data) (fun TxInfo [Maybe (con bytestring)]))
                    )
                    (lam
                      ds
                      (con data)
                      (lam
                        ds
                        TxInfo
                        [
                          { [ TxInfo_match ds ] [Maybe (con bytestring)] }
                          (lam
                            ds
                            [List TxInInfo]
                            (lam
                              ds
                              [List TxOut]
                              (lam
                                ds
                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                (lam
                                  ds
                                  [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                  (lam
                                    ds
                                    [List DCert]
                                    (lam
                                      ds
                                      [List [[Tuple2 StakingCredential] (con integer)]]
                                      (lam
                                        ds
                                        [Interval (con integer)]
                                        (lam
                                          ds
                                          [List (con bytestring)]
                                          (lam
                                            ds
                                            [List [[Tuple2 (con bytestring)] (con data)]]
                                            (lam
                                              ds
                                              (con bytestring)
                                              (force
                                                [
                                                  [
                                                    {
                                                      [
                                                        {
                                                          Maybe_match
                                                          [[Tuple2 (con bytestring)] (con data)]
                                                        }
                                                        [
                                                          [
                                                            [
                                                              {
                                                                {
                                                                  fFoldableNil_cfoldMap
                                                                  [(lam a (type) [Maybe a]) [[Tuple2 (con bytestring)] (con data)]]
                                                                }
                                                                [[Tuple2 (con bytestring)] (con data)]
                                                              }
                                                              {
                                                                fMonoidFirst
                                                                [[Tuple2 (con bytestring)] (con data)]
                                                              }
                                                            ]
                                                            (lam
                                                              x
                                                              [[Tuple2 (con bytestring)] (con data)]
                                                              [
                                                                {
                                                                  [
                                                                    {
                                                                      {
                                                                        Tuple2_match
                                                                        (con bytestring)
                                                                      }
                                                                      (con data)
                                                                    }
                                                                    x
                                                                  ]
                                                                  [Maybe [[Tuple2 (con bytestring)] (con data)]]
                                                                }
                                                                (lam
                                                                  ds
                                                                  (con bytestring)
                                                                  (lam
                                                                    ds
                                                                    (con data)
                                                                    (force
                                                                      [
                                                                        [
                                                                          {
                                                                            [
                                                                              Bool_match
                                                                              [
                                                                                [
                                                                                  [
                                                                                    {
                                                                                      (builtin
                                                                                        ifThenElse
                                                                                      )
                                                                                      Bool
                                                                                    }
                                                                                    [
                                                                                      [
                                                                                        (builtin
                                                                                          equalsData
                                                                                        )
                                                                                        ds
                                                                                      ]
                                                                                      ds
                                                                                    ]
                                                                                  ]
                                                                                  True
                                                                                ]
                                                                                False
                                                                              ]
                                                                            ]
                                                                            (delayed [Maybe [[Tuple2 (con bytestring)] (con data)]])
                                                                          }
                                                                          (delay
                                                                            [
                                                                              {
                                                                                Just
                                                                                [[Tuple2 (con bytestring)] (con data)]
                                                                              }
                                                                              x
                                                                            ]
                                                                          )
                                                                        ]
                                                                        (delay
                                                                          {
                                                                            Nothing
                                                                            [[Tuple2 (con bytestring)] (con data)]
                                                                          }
                                                                        )
                                                                      ]
                                                                    )
                                                                  )
                                                                )
                                                              ]
                                                            )
                                                          ]
                                                          ds
                                                        ]
                                                      ]
                                                      (delayed [Maybe (con bytestring)])
                                                    }
                                                    (lam
                                                      a
                                                      [[Tuple2 (con bytestring)] (con data)]
                                                      (delay
                                                        [
                                                          {
                                                            Just
                                                            (con bytestring)
                                                          }
                                                          [
                                                            {
                                                              [
                                                                {
                                                                  {
                                                                    Tuple2_match
                                                                    (con bytestring)
                                                                  }
                                                                  (con data)
                                                                }
                                                                a
                                                              ]
                                                              (con bytestring)
                                                            }
                                                            (lam
                                                              a
                                                              (con bytestring)
                                                              (lam
                                                                ds (con data) a
                                                              )
                                                            )
                                                          ]
                                                        ]
                                                      )
                                                    )
                                                  ]
                                                  (delay
                                                    { Nothing (con bytestring) }
                                                  )
                                                ]
                                              )
                                            )
                                          )
                                        )
                                      )
                                    )
                                  )
                                )
                              )
                            )
                          )
                        ]
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      fEqCredential_c (fun Credential (fun Credential Bool))
                    )
                    (lam
                      ds
                      Credential
                      (lam
                        ds
                        Credential
                        [
                          [
                            { [ Credential_match ds ] Bool }
                            (lam
                              l
                              (con bytestring)
                              [
                                [
                                  { [ Credential_match ds ] Bool }
                                  (lam
                                    r
                                    (con bytestring)
                                    [ [ equalsByteString l ] r ]
                                  )
                                ]
                                (lam ipv (con bytestring) False)
                              ]
                            )
                          ]
                          (lam
                            a
                            (con bytestring)
                            [
                              [
                                { [ Credential_match ds ] Bool }
                                (lam ipv (con bytestring) False)
                              ]
                              (lam
                                a (con bytestring) [ [ equalsByteString a ] a ]
                              )
                            ]
                          )
                        ]
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      equalsInteger (fun (con integer) (fun (con integer) Bool))
                    )
                    (lam
                      x
                      (con integer)
                      (lam
                        y
                        (con integer)
                        [
                          [
                            [
                              { (builtin ifThenElse) Bool }
                              [ [ (builtin equalsInteger) x ] y ]
                            ]
                            True
                          ]
                          False
                        ]
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      fEqStakingCredential_c
                      (fun StakingCredential (fun StakingCredential Bool))
                    )
                    (lam
                      ds
                      StakingCredential
                      (lam
                        ds
                        StakingCredential
                        [
                          [
                            { [ StakingCredential_match ds ] Bool }
                            (lam
                              l
                              Credential
                              [
                                [
                                  { [ StakingCredential_match ds ] Bool }
                                  (lam r Credential [ [ fEqCredential_c l ] r ])
                                ]
                                (lam
                                  ipv
                                  (con integer)
                                  (lam
                                    ipv
                                    (con integer)
                                    (lam ipv (con integer) False)
                                  )
                                )
                              ]
                            )
                          ]
                          (lam
                            a
                            (con integer)
                            (lam
                              b
                              (con integer)
                              (lam
                                c
                                (con integer)
                                [
                                  [
                                    { [ StakingCredential_match ds ] Bool }
                                    (lam ipv Credential False)
                                  ]
                                  (lam
                                    a
                                    (con integer)
                                    (lam
                                      b
                                      (con integer)
                                      (lam
                                        c
                                        (con integer)
                                        (force
                                          [
                                            [
                                              {
                                                [
                                                  Bool_match
                                                  [
                                                    [
                                                      [
                                                        {
                                                          (builtin ifThenElse)
                                                          Bool
                                                        }
                                                        [
                                                          [
                                                            (builtin
                                                              equalsInteger
                                                            )
                                                            a
                                                          ]
                                                          a
                                                        ]
                                                      ]
                                                      True
                                                    ]
                                                    False
                                                  ]
                                                ]
                                                (delayed Bool)
                                              }
                                              (delay
                                                (force
                                                  [
                                                    [
                                                      {
                                                        [
                                                          Bool_match
                                                          [
                                                            [
                                                              [
                                                                {
                                                                  (builtin
                                                                    ifThenElse
                                                                  )
                                                                  Bool
                                                                }
                                                                [
                                                                  [
                                                                    (builtin
                                                                      equalsInteger
                                                                    )
                                                                    b
                                                                  ]
                                                                  b
                                                                ]
                                                              ]
                                                              True
                                                            ]
                                                            False
                                                          ]
                                                        ]
                                                        (delayed Bool)
                                                      }
                                                      (delay
                                                        [
                                                          [ equalsInteger c ] c
                                                        ]
                                                      )
                                                    ]
                                                    (delay False)
                                                  ]
                                                )
                                              )
                                            ]
                                            (delay False)
                                          ]
                                        )
                                      )
                                    )
                                  )
                                ]
                              )
                            )
                          )
                        ]
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl fEqAddress_c (fun Address (fun Address Bool)))
                    (lam
                      ds
                      Address
                      (lam
                        ds
                        Address
                        [
                          { [ Address_match ds ] Bool }
                          (lam
                            cred
                            Credential
                            (lam
                              stakingCred
                              [Maybe StakingCredential]
                              [
                                { [ Address_match ds ] Bool }
                                (lam
                                  cred
                                  Credential
                                  (lam
                                    stakingCred
                                    [Maybe StakingCredential]
                                    (let
                                      (nonrec)
                                      (termbind
                                        (nonstrict)
                                        (vardecl j Bool)
                                        (force
                                          [
                                            [
                                              {
                                                [
                                                  {
                                                    Maybe_match
                                                    StakingCredential
                                                  }
                                                  stakingCred
                                                ]
                                                (delayed Bool)
                                              }
                                              (lam
                                                a
                                                StakingCredential
                                                (delay
                                                  (force
                                                    [
                                                      [
                                                        {
                                                          [
                                                            {
                                                              Maybe_match
                                                              StakingCredential
                                                            }
                                                            stakingCred
                                                          ]
                                                          (delayed Bool)
                                                        }
                                                        (lam
                                                          a
                                                          StakingCredential
                                                          (delay
                                                            [
                                                              [
                                                                fEqStakingCredential_c
                                                                a
                                                              ]
                                                              a
                                                            ]
                                                          )
                                                        )
                                                      ]
                                                      (delay False)
                                                    ]
                                                  )
                                                )
                                              )
                                            ]
                                            (delay
                                              (force
                                                [
                                                  [
                                                    {
                                                      [
                                                        {
                                                          Maybe_match
                                                          StakingCredential
                                                        }
                                                        stakingCred
                                                      ]
                                                      (delayed Bool)
                                                    }
                                                    (lam
                                                      ipv
                                                      StakingCredential
                                                      (delay False)
                                                    )
                                                  ]
                                                  (delay True)
                                                ]
                                              )
                                            )
                                          ]
                                        )
                                      )
                                      [
                                        [
                                          { [ Credential_match cred ] Bool }
                                          (lam
                                            l
                                            (con bytestring)
                                            [
                                              [
                                                {
                                                  [ Credential_match cred ] Bool
                                                }
                                                (lam
                                                  r
                                                  (con bytestring)
                                                  (force
                                                    [
                                                      [
                                                        {
                                                          [
                                                            Bool_match
                                                            [
                                                              [
                                                                [
                                                                  {
                                                                    (builtin
                                                                      ifThenElse
                                                                    )
                                                                    Bool
                                                                  }
                                                                  [
                                                                    [
                                                                      (builtin
                                                                        equalsByteString
                                                                      )
                                                                      l
                                                                    ]
                                                                    r
                                                                  ]
                                                                ]
                                                                True
                                                              ]
                                                              False
                                                            ]
                                                          ]
                                                          (delayed Bool)
                                                        }
                                                        (delay j)
                                                      ]
                                                      (delay False)
                                                    ]
                                                  )
                                                )
                                              ]
                                              (lam ipv (con bytestring) False)
                                            ]
                                          )
                                        ]
                                        (lam
                                          a
                                          (con bytestring)
                                          [
                                            [
                                              { [ Credential_match cred ] Bool }
                                              (lam ipv (con bytestring) False)
                                            ]
                                            (lam
                                              a
                                              (con bytestring)
                                              (force
                                                [
                                                  [
                                                    {
                                                      [
                                                        Bool_match
                                                        [
                                                          [
                                                            [
                                                              {
                                                                (builtin
                                                                  ifThenElse
                                                                )
                                                                Bool
                                                              }
                                                              [
                                                                [
                                                                  (builtin
                                                                    equalsByteString
                                                                  )
                                                                  a
                                                                ]
                                                                a
                                                              ]
                                                            ]
                                                            True
                                                          ]
                                                          False
                                                        ]
                                                      ]
                                                      (delayed Bool)
                                                    }
                                                    (delay j)
                                                  ]
                                                  (delay False)
                                                ]
                                              )
                                            )
                                          ]
                                        )
                                      ]
                                    )
                                  )
                                )
                              ]
                            )
                          )
                        ]
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl error (all a (type) (fun (con unit) a)))
                    (abs a (type) (lam thunk (con unit) (error a)))
                  )
                  (termbind
                    (strict)
                    (vardecl findOwnInput (fun ScriptContext [Maybe TxInInfo]))
                    (lam
                      ds
                      ScriptContext
                      [
                        { [ ScriptContext_match ds ] [Maybe TxInInfo] }
                        (lam
                          ds
                          TxInfo
                          (lam
                            ds
                            ScriptPurpose
                            [
                              { [ TxInfo_match ds ] [Maybe TxInInfo] }
                              (lam
                                ds
                                [List TxInInfo]
                                (lam
                                  ds
                                  [List TxOut]
                                  (lam
                                    ds
                                    [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                    (lam
                                      ds
                                      [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                      (lam
                                        ds
                                        [List DCert]
                                        (lam
                                          ds
                                          [List [[Tuple2 StakingCredential] (con integer)]]
                                          (lam
                                            ds
                                            [Interval (con integer)]
                                            (lam
                                              ds
                                              [List (con bytestring)]
                                              (lam
                                                ds
                                                [List [[Tuple2 (con bytestring)] (con data)]]
                                                (lam
                                                  ds
                                                  (con bytestring)
                                                  (force
                                                    [
                                                      [
                                                        [
                                                          [
                                                            {
                                                              [
                                                                ScriptPurpose_match
                                                                ds
                                                              ]
                                                              (delayed [Maybe TxInInfo])
                                                            }
                                                            (lam
                                                              default_arg0
                                                              DCert
                                                              (delay
                                                                {
                                                                  Nothing
                                                                  TxInInfo
                                                                }
                                                              )
                                                            )
                                                          ]
                                                          (lam
                                                            default_arg0
                                                            (con bytestring)
                                                            (delay
                                                              {
                                                                Nothing TxInInfo
                                                              }
                                                            )
                                                          )
                                                        ]
                                                        (lam
                                                          default_arg0
                                                          StakingCredential
                                                          (delay
                                                            { Nothing TxInInfo }
                                                          )
                                                        )
                                                      ]
                                                      (lam
                                                        txOutRef
                                                        TxOutRef
                                                        (delay
                                                          [
                                                            [
                                                              [
                                                                {
                                                                  {
                                                                    fFoldableNil_cfoldMap
                                                                    [(lam a (type) [Maybe a]) TxInInfo]
                                                                  }
                                                                  TxInInfo
                                                                }
                                                                {
                                                                  fMonoidFirst
                                                                  TxInInfo
                                                                }
                                                              ]
                                                              (lam
                                                                x
                                                                TxInInfo
                                                                [
                                                                  {
                                                                    [
                                                                      TxInInfo_match
                                                                      x
                                                                    ]
                                                                    [Maybe TxInInfo]
                                                                  }
                                                                  (lam
                                                                    ds
                                                                    TxOutRef
                                                                    (lam
                                                                      ds
                                                                      TxOut
                                                                      (force
                                                                        [
                                                                          [
                                                                            {
                                                                              [
                                                                                Bool_match
                                                                                [
                                                                                  [
                                                                                    fEqTxOutRef_c
                                                                                    ds
                                                                                  ]
                                                                                  txOutRef
                                                                                ]
                                                                              ]
                                                                              (delayed [Maybe TxInInfo])
                                                                            }
                                                                            (delay
                                                                              [
                                                                                {
                                                                                  Just
                                                                                  TxInInfo
                                                                                }
                                                                                x
                                                                              ]
                                                                            )
                                                                          ]
                                                                          (delay
                                                                            {
                                                                              Nothing
                                                                              TxInInfo
                                                                            }
                                                                          )
                                                                        ]
                                                                      )
                                                                    )
                                                                  )
                                                                ]
                                                              )
                                                            ]
                                                            ds
                                                          ]
                                                        )
                                                      )
                                                    ]
                                                  )
                                                )
                                              )
                                            )
                                          )
                                        )
                                      )
                                    )
                                  )
                                )
                              )
                            ]
                          )
                        )
                      ]
                    )
                  )
                  (datatypebind
                    (datatype
                      (tyvardecl Unit (type))  Unit_match (vardecl Unit Unit)
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      getContinuingOutputs (fun ScriptContext [List TxOut])
                    )
                    (lam
                      ctx
                      ScriptContext
                      (force
                        [
                          [
                            {
                              [ { Maybe_match TxInInfo } [ findOwnInput ctx ] ]
                              (delayed [List TxOut])
                            }
                            (lam
                              ds
                              TxInInfo
                              (delay
                                [
                                  { [ TxInInfo_match ds ] [List TxOut] }
                                  (lam
                                    ds
                                    TxOutRef
                                    (lam
                                      ds
                                      TxOut
                                      [
                                        { [ TxOut_match ds ] [List TxOut] }
                                        (lam
                                          ds
                                          Address
                                          (lam
                                            ds
                                            [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                            (lam
                                              ds
                                              [Maybe (con bytestring)]
                                              [
                                                {
                                                  [ ScriptContext_match ctx ]
                                                  [List TxOut]
                                                }
                                                (lam
                                                  ds
                                                  TxInfo
                                                  (lam
                                                    ds
                                                    ScriptPurpose
                                                    [
                                                      {
                                                        [ TxInfo_match ds ]
                                                        [List TxOut]
                                                      }
                                                      (lam
                                                        ds
                                                        [List TxInInfo]
                                                        (lam
                                                          ds
                                                          [List TxOut]
                                                          (lam
                                                            ds
                                                            [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                            (lam
                                                              ds
                                                              [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                              (lam
                                                                ds
                                                                [List DCert]
                                                                (lam
                                                                  ds
                                                                  [List [[Tuple2 StakingCredential] (con integer)]]
                                                                  (lam
                                                                    ds
                                                                    [Interval (con integer)]
                                                                    (lam
                                                                      ds
                                                                      [List (con bytestring)]
                                                                      (lam
                                                                        ds
                                                                        [List [[Tuple2 (con bytestring)] (con data)]]
                                                                        (lam
                                                                          ds
                                                                          (con bytestring)
                                                                          [
                                                                            [
                                                                              [
                                                                                {
                                                                                  {
                                                                                    foldr
                                                                                    TxOut
                                                                                  }
                                                                                  [List TxOut]
                                                                                }
                                                                                (lam
                                                                                  e
                                                                                  TxOut
                                                                                  (lam
                                                                                    xs
                                                                                    [List TxOut]
                                                                                    [
                                                                                      {
                                                                                        [
                                                                                          TxOut_match
                                                                                          e
                                                                                        ]
                                                                                        [List TxOut]
                                                                                      }
                                                                                      (lam
                                                                                        ds
                                                                                        Address
                                                                                        (lam
                                                                                          ds
                                                                                          [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                          (lam
                                                                                            ds
                                                                                            [Maybe (con bytestring)]
                                                                                            (force
                                                                                              [
                                                                                                [
                                                                                                  {
                                                                                                    [
                                                                                                      Bool_match
                                                                                                      [
                                                                                                        [
                                                                                                          fEqAddress_c
                                                                                                          ds
                                                                                                        ]
                                                                                                        ds
                                                                                                      ]
                                                                                                    ]
                                                                                                    (delayed [List TxOut])
                                                                                                  }
                                                                                                  (delay
                                                                                                    [
                                                                                                      [
                                                                                                        {
                                                                                                          Cons
                                                                                                          TxOut
                                                                                                        }
                                                                                                        e
                                                                                                      ]
                                                                                                      xs
                                                                                                    ]
                                                                                                  )
                                                                                                ]
                                                                                                (delay
                                                                                                  xs
                                                                                                )
                                                                                              ]
                                                                                            )
                                                                                          )
                                                                                        )
                                                                                      )
                                                                                    ]
                                                                                  )
                                                                                )
                                                                              ]
                                                                              {
                                                                                Nil
                                                                                TxOut
                                                                              }
                                                                            ]
                                                                            ds
                                                                          ]
                                                                        )
                                                                      )
                                                                    )
                                                                  )
                                                                )
                                                              )
                                                            )
                                                          )
                                                        )
                                                      )
                                                    ]
                                                  )
                                                )
                                              ]
                                            )
                                          )
                                        )
                                      ]
                                    )
                                  )
                                ]
                              )
                            )
                          ]
                          (delay
                            [
                              { error [List TxOut] }
                              [
                                {
                                  [
                                    Unit_match
                                    [
                                      [
                                        { (builtin chooseUnit) Unit }
                                        [
                                          (builtin trace)
                                          (con
                                            string
                                              "Can't get any continuing outputs"
                                          )
                                        ]
                                      ]
                                      Unit
                                    ]
                                  ]
                                  (con unit)
                                }
                                (con unit ())
                              ]
                            ]
                          )
                        ]
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      checkOwnOutputConstraint
                      (all o (type) (fun [(lam a (type) (fun a (con data))) o] (fun ScriptContext (fun [OutputConstraint o] Bool))))
                    )
                    (abs
                      o
                      (type)
                      (lam
                        dToData
                        [(lam a (type) (fun a (con data))) o]
                        (lam
                          ctx
                          ScriptContext
                          (lam
                            ds
                            [OutputConstraint o]
                            [
                              { [ ScriptContext_match ctx ] Bool }
                              (lam
                                ds
                                TxInfo
                                (lam
                                  ds
                                  ScriptPurpose
                                  [
                                    { [ { OutputConstraint_match o } ds ] Bool }
                                    (lam
                                      ds
                                      o
                                      (lam
                                        ds
                                        [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                        (let
                                          (nonrec)
                                          (termbind
                                            (nonstrict)
                                            (vardecl
                                              hsh [Maybe (con bytestring)]
                                            )
                                            [
                                              [ findDatumHash [ dToData ds ] ]
                                              ds
                                            ]
                                          )
                                          (force
                                            [
                                              [
                                                {
                                                  [
                                                    Bool_match
                                                    [
                                                      [
                                                        [
                                                          {
                                                            {
                                                              fFoldableNil_cfoldMap
                                                              [(lam a (type) a) Bool]
                                                            }
                                                            TxOut
                                                          }
                                                          [
                                                            { fMonoidSum Bool }
                                                            fAdditiveMonoidBool
                                                          ]
                                                        ]
                                                        (lam
                                                          ds
                                                          TxOut
                                                          [
                                                            {
                                                              [ TxOut_match ds ]
                                                              Bool
                                                            }
                                                            (lam
                                                              ds
                                                              Address
                                                              (lam
                                                                ds
                                                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                (lam
                                                                  ds
                                                                  [Maybe (con bytestring)]
                                                                  (force
                                                                    [
                                                                      [
                                                                        {
                                                                          [
                                                                            {
                                                                              Maybe_match
                                                                              (con bytestring)
                                                                            }
                                                                            ds
                                                                          ]
                                                                          (delayed Bool)
                                                                        }
                                                                        (lam
                                                                          svh
                                                                          (con bytestring)
                                                                          (delay
                                                                            (force
                                                                              [
                                                                                [
                                                                                  {
                                                                                    [
                                                                                      Bool_match
                                                                                      [
                                                                                        [
                                                                                          [
                                                                                            checkBinRel
                                                                                            equalsInteger
                                                                                          ]
                                                                                          ds
                                                                                        ]
                                                                                        ds
                                                                                      ]
                                                                                    ]
                                                                                    (delayed Bool)
                                                                                  }
                                                                                  (delay
                                                                                    (force
                                                                                      [
                                                                                        [
                                                                                          {
                                                                                            [
                                                                                              {
                                                                                                Maybe_match
                                                                                                (con bytestring)
                                                                                              }
                                                                                              hsh
                                                                                            ]
                                                                                            (delayed Bool)
                                                                                          }
                                                                                          (lam
                                                                                            a
                                                                                            (con bytestring)
                                                                                            (delay
                                                                                              [
                                                                                                [
                                                                                                  equalsByteString
                                                                                                  a
                                                                                                ]
                                                                                                svh
                                                                                              ]
                                                                                            )
                                                                                          )
                                                                                        ]
                                                                                        (delay
                                                                                          False
                                                                                        )
                                                                                      ]
                                                                                    )
                                                                                  )
                                                                                ]
                                                                                (delay
                                                                                  False
                                                                                )
                                                                              ]
                                                                            )
                                                                          )
                                                                        )
                                                                      ]
                                                                      (delay
                                                                        False
                                                                      )
                                                                    ]
                                                                  )
                                                                )
                                                              )
                                                            )
                                                          ]
                                                        )
                                                      ]
                                                      [
                                                        getContinuingOutputs ctx
                                                      ]
                                                    ]
                                                  ]
                                                  (delayed Bool)
                                                }
                                                (delay True)
                                              ]
                                              (delay
                                                [
                                                  [
                                                    {
                                                      (builtin chooseUnit) Bool
                                                    }
                                                    [
                                                      (builtin trace)
                                                      (con
                                                        string
                                                          "Output constraint"
                                                      )
                                                    ]
                                                  ]
                                                  False
                                                ]
                                              )
                                            ]
                                          )
                                        )
                                      )
                                    )
                                  ]
                                )
                              )
                            ]
                          )
                        )
                      )
                    )
                  )
                  (datatypebind
                    (datatype
                      (tyvardecl Ordering (type))

                      Ordering_match
                      (vardecl EQ Ordering)
                      (vardecl GT Ordering)
                      (vardecl LT Ordering)
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      fOrdData_ccompare
                      (fun (con integer) (fun (con integer) Ordering))
                    )
                    (lam
                      x
                      (con integer)
                      (lam
                        y
                        (con integer)
                        (force
                          [
                            [
                              {
                                [
                                  Bool_match
                                  [
                                    [
                                      [
                                        { (builtin ifThenElse) Bool }
                                        [ [ (builtin equalsInteger) x ] y ]
                                      ]
                                      True
                                    ]
                                    False
                                  ]
                                ]
                                (delayed Ordering)
                              }
                              (delay EQ)
                            ]
                            (delay
                              (force
                                [
                                  [
                                    {
                                      [
                                        Bool_match
                                        [
                                          [
                                            [
                                              { (builtin ifThenElse) Bool }
                                              [
                                                [
                                                  (builtin lessThanEqualsInteger
                                                  )
                                                  x
                                                ]
                                                y
                                              ]
                                            ]
                                            True
                                          ]
                                          False
                                        ]
                                      ]
                                      (delayed Ordering)
                                    }
                                    (delay LT)
                                  ]
                                  (delay GT)
                                ]
                              )
                            )
                          ]
                        )
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      fOrdInteger_cmax
                      (fun (con integer) (fun (con integer) (con integer)))
                    )
                    (lam
                      x
                      (con integer)
                      (lam
                        y
                        (con integer)
                        (force
                          [
                            [
                              {
                                [
                                  Bool_match
                                  [
                                    [
                                      [
                                        { (builtin ifThenElse) Bool }
                                        [
                                          [ (builtin lessThanEqualsInteger) x ]
                                          y
                                        ]
                                      ]
                                      True
                                    ]
                                    False
                                  ]
                                ]
                                (delayed (con integer))
                              }
                              (delay y)
                            ]
                            (delay x)
                          ]
                        )
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      fOrdInteger_cmin
                      (fun (con integer) (fun (con integer) (con integer)))
                    )
                    (lam
                      x
                      (con integer)
                      (lam
                        y
                        (con integer)
                        (force
                          [
                            [
                              {
                                [
                                  Bool_match
                                  [
                                    [
                                      [
                                        { (builtin ifThenElse) Bool }
                                        [
                                          [ (builtin lessThanEqualsInteger) x ]
                                          y
                                        ]
                                      ]
                                      True
                                    ]
                                    False
                                  ]
                                ]
                                (delayed (con integer))
                              }
                              (delay x)
                            ]
                            (delay y)
                          ]
                        )
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      greaterThanEqInteger
                      (fun (con integer) (fun (con integer) Bool))
                    )
                    (lam
                      x
                      (con integer)
                      (lam
                        y
                        (con integer)
                        [
                          [
                            [
                              { (builtin ifThenElse) Bool }
                              [ [ (builtin greaterThanEqualsInteger) x ] y ]
                            ]
                            True
                          ]
                          False
                        ]
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      greaterThanInteger
                      (fun (con integer) (fun (con integer) Bool))
                    )
                    (lam
                      x
                      (con integer)
                      (lam
                        y
                        (con integer)
                        [
                          [
                            [
                              { (builtin ifThenElse) Bool }
                              [ [ (builtin greaterThanInteger) x ] y ]
                            ]
                            True
                          ]
                          False
                        ]
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      lessThanInteger
                      (fun (con integer) (fun (con integer) Bool))
                    )
                    (lam
                      x
                      (con integer)
                      (lam
                        y
                        (con integer)
                        [
                          [
                            [
                              { (builtin ifThenElse) Bool }
                              [ [ (builtin lessThanInteger) x ] y ]
                            ]
                            True
                          ]
                          False
                        ]
                      )
                    )
                  )
                  (datatypebind
                    (datatype
                      (tyvardecl Ord (fun (type) (type)))
                      (tyvardecl a (type))
                      Ord_match
                      (vardecl
                        CConsOrd
                        (fun [(lam a (type) (fun a (fun a Bool))) a] (fun (fun a (fun a Ordering)) (fun (fun a (fun a Bool)) (fun (fun a (fun a Bool)) (fun (fun a (fun a Bool)) (fun (fun a (fun a Bool)) (fun (fun a (fun a a)) (fun (fun a (fun a a)) [Ord a]))))))))
                      )
                    )
                  )
                  (termbind
                    (nonstrict)
                    (vardecl fOrdPOSIXTime [Ord (con integer)])
                    [
                      [
                        [
                          [
                            [
                              [
                                [
                                  [ { CConsOrd (con integer) } equalsInteger ]
                                  fOrdData_ccompare
                                ]
                                lessThanInteger
                              ]
                              lessThanEqInteger
                            ]
                            greaterThanInteger
                          ]
                          greaterThanEqInteger
                        ]
                        fOrdInteger_cmax
                      ]
                      fOrdInteger_cmin
                    ]
                  )
                  (termbind
                    (strict)
                    (vardecl
                      compare
                      (all a (type) (fun [Ord a] (fun a (fun a Ordering))))
                    )
                    (abs
                      a
                      (type)
                      (lam
                        v
                        [Ord a]
                        [
                          { [ { Ord_match a } v ] (fun a (fun a Ordering)) }
                          (lam
                            v
                            [(lam a (type) (fun a (fun a Bool))) a]
                            (lam
                              v
                              (fun a (fun a Ordering))
                              (lam
                                v
                                (fun a (fun a Bool))
                                (lam
                                  v
                                  (fun a (fun a Bool))
                                  (lam
                                    v
                                    (fun a (fun a Bool))
                                    (lam
                                      v
                                      (fun a (fun a Bool))
                                      (lam
                                        v
                                        (fun a (fun a a))
                                        (lam v (fun a (fun a a)) v)
                                      )
                                    )
                                  )
                                )
                              )
                            )
                          )
                        ]
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      hull_ccompare
                      (all a (type) (fun [Ord a] (fun [Extended a] (fun [Extended a] Ordering))))
                    )
                    (abs
                      a
                      (type)
                      (lam
                        dOrd
                        [Ord a]
                        (lam
                          ds
                          [Extended a]
                          (lam
                            ds
                            [Extended a]
                            (let
                              (nonrec)
                              (termbind
                                (strict)
                                (vardecl fail (fun (all a (type) a) Ordering))
                                (lam ds (all a (type) a) (error Ordering))
                              )
                              (termbind
                                (strict)
                                (vardecl fail (fun (all a (type) a) Ordering))
                                (lam
                                  ds
                                  (all a (type) a)
                                  (force
                                    [
                                      [
                                        [
                                          {
                                            [ { Extended_match a } ds ]
                                            (delayed Ordering)
                                          }
                                          (lam
                                            default_arg0
                                            a
                                            (delay
                                              (force
                                                [
                                                  [
                                                    [
                                                      {
                                                        [
                                                          { Extended_match a }
                                                          ds
                                                        ]
                                                        (delayed Ordering)
                                                      }
                                                      (lam
                                                        l
                                                        a
                                                        (delay
                                                          (force
                                                            [
                                                              [
                                                                [
                                                                  {
                                                                    [
                                                                      {
                                                                        Extended_match
                                                                        a
                                                                      }
                                                                      ds
                                                                    ]
                                                                    (delayed Ordering)
                                                                  }
                                                                  (lam
                                                                    r
                                                                    a
                                                                    (delay
                                                                      [
                                                                        [
                                                                          [
                                                                            {
                                                                              compare
                                                                              a
                                                                            }
                                                                            dOrd
                                                                          ]
                                                                          l
                                                                        ]
                                                                        r
                                                                      ]
                                                                    )
                                                                  )
                                                                ]
                                                                (delay
                                                                  [
                                                                    fail
                                                                    (abs
                                                                      e
                                                                      (type)
                                                                      (error e)
                                                                    )
                                                                  ]
                                                                )
                                                              ]
                                                              (delay
                                                                [
                                                                  fail
                                                                  (abs
                                                                    e
                                                                    (type)
                                                                    (error e)
                                                                  )
                                                                ]
                                                              )
                                                            ]
                                                          )
                                                        )
                                                      )
                                                    ]
                                                    (delay
                                                      [
                                                        fail
                                                        (abs e (type) (error e))
                                                      ]
                                                    )
                                                  ]
                                                  (delay GT)
                                                ]
                                              )
                                            )
                                          )
                                        ]
                                        (delay
                                          (force
                                            [
                                              [
                                                [
                                                  {
                                                    [ { Extended_match a } ds ]
                                                    (delayed Ordering)
                                                  }
                                                  (lam
                                                    l
                                                    a
                                                    (delay
                                                      (force
                                                        [
                                                          [
                                                            [
                                                              {
                                                                [
                                                                  {
                                                                    Extended_match
                                                                    a
                                                                  }
                                                                  ds
                                                                ]
                                                                (delayed Ordering)
                                                              }
                                                              (lam
                                                                r
                                                                a
                                                                (delay
                                                                  [
                                                                    [
                                                                      [
                                                                        {
                                                                          compare
                                                                          a
                                                                        }
                                                                        dOrd
                                                                      ]
                                                                      l
                                                                    ]
                                                                    r
                                                                  ]
                                                                )
                                                              )
                                                            ]
                                                            (delay
                                                              [
                                                                fail
                                                                (abs
                                                                  e
                                                                  (type)
                                                                  (error e)
                                                                )
                                                              ]
                                                            )
                                                          ]
                                                          (delay
                                                            [
                                                              fail
                                                              (abs
                                                                e
                                                                (type)
                                                                (error e)
                                                              )
                                                            ]
                                                          )
                                                        ]
                                                      )
                                                    )
                                                  )
                                                ]
                                                (delay
                                                  [
                                                    fail
                                                    (abs e (type) (error e))
                                                  ]
                                                )
                                              ]
                                              (delay GT)
                                            ]
                                          )
                                        )
                                      ]
                                      (delay LT)
                                    ]
                                  )
                                )
                              )
                              (force
                                [
                                  [
                                    [
                                      {
                                        [ { Extended_match a } ds ]
                                        (delayed Ordering)
                                      }
                                      (lam
                                        default_arg0
                                        a
                                        (let
                                          (nonrec)
                                          (termbind
                                            (strict)
                                            (vardecl
                                              fail
                                              (fun (all a (type) a) Ordering)
                                            )
                                            (lam
                                              ds
                                              (all a (type) a)
                                              (force
                                                [
                                                  [
                                                    [
                                                      {
                                                        [
                                                          { Extended_match a }
                                                          ds
                                                        ]
                                                        (delayed Ordering)
                                                      }
                                                      (lam
                                                        default_arg0
                                                        a
                                                        (delay
                                                          (force
                                                            [
                                                              [
                                                                [
                                                                  {
                                                                    [
                                                                      {
                                                                        Extended_match
                                                                        a
                                                                      }
                                                                      ds
                                                                    ]
                                                                    (delayed Ordering)
                                                                  }
                                                                  (lam
                                                                    l
                                                                    a
                                                                    (delay
                                                                      (force
                                                                        [
                                                                          [
                                                                            [
                                                                              {
                                                                                [
                                                                                  {
                                                                                    Extended_match
                                                                                    a
                                                                                  }
                                                                                  ds
                                                                                ]
                                                                                (delayed Ordering)
                                                                              }
                                                                              (lam
                                                                                r
                                                                                a
                                                                                (delay
                                                                                  [
                                                                                    [
                                                                                      [
                                                                                        {
                                                                                          compare
                                                                                          a
                                                                                        }
                                                                                        dOrd
                                                                                      ]
                                                                                      l
                                                                                    ]
                                                                                    r
                                                                                  ]
                                                                                )
                                                                              )
                                                                            ]
                                                                            (delay
                                                                              [
                                                                                fail
                                                                                (abs
                                                                                  e
                                                                                  (type)
                                                                                  (error
                                                                                    e
                                                                                  )
                                                                                )
                                                                              ]
                                                                            )
                                                                          ]
                                                                          (delay
                                                                            [
                                                                              fail
                                                                              (abs
                                                                                e
                                                                                (type)
                                                                                (error
                                                                                  e
                                                                                )
                                                                              )
                                                                            ]
                                                                          )
                                                                        ]
                                                                      )
                                                                    )
                                                                  )
                                                                ]
                                                                (delay
                                                                  [
                                                                    fail
                                                                    (abs
                                                                      e
                                                                      (type)
                                                                      (error e)
                                                                    )
                                                                  ]
                                                                )
                                                              ]
                                                              (delay GT)
                                                            ]
                                                          )
                                                        )
                                                      )
                                                    ]
                                                    (delay
                                                      (force
                                                        [
                                                          [
                                                            [
                                                              {
                                                                [
                                                                  {
                                                                    Extended_match
                                                                    a
                                                                  }
                                                                  ds
                                                                ]
                                                                (delayed Ordering)
                                                              }
                                                              (lam
                                                                l
                                                                a
                                                                (delay
                                                                  (force
                                                                    [
                                                                      [
                                                                        [
                                                                          {
                                                                            [
                                                                              {
                                                                                Extended_match
                                                                                a
                                                                              }
                                                                              ds
                                                                            ]
                                                                            (delayed Ordering)
                                                                          }
                                                                          (lam
                                                                            r
                                                                            a
                                                                            (delay
                                                                              [
                                                                                [
                                                                                  [
                                                                                    {
                                                                                      compare
                                                                                      a
                                                                                    }
                                                                                    dOrd
                                                                                  ]
                                                                                  l
                                                                                ]
                                                                                r
                                                                              ]
                                                                            )
                                                                          )
                                                                        ]
                                                                        (delay
                                                                          [
                                                                            fail
                                                                            (abs
                                                                              e
                                                                              (type)
                                                                              (error
                                                                                e
                                                                              )
                                                                            )
                                                                          ]
                                                                        )
                                                                      ]
                                                                      (delay
                                                                        [
                                                                          fail
                                                                          (abs
                                                                            e
                                                                            (type)
                                                                            (error
                                                                              e
                                                                            )
                                                                          )
                                                                        ]
                                                                      )
                                                                    ]
                                                                  )
                                                                )
                                                              )
                                                            ]
                                                            (delay
                                                              [
                                                                fail
                                                                (abs
                                                                  e
                                                                  (type)
                                                                  (error e)
                                                                )
                                                              ]
                                                            )
                                                          ]
                                                          (delay GT)
                                                        ]
                                                      )
                                                    )
                                                  ]
                                                  (delay LT)
                                                ]
                                              )
                                            )
                                          )
                                          (delay
                                            (force
                                              [
                                                [
                                                  [
                                                    {
                                                      [
                                                        { Extended_match a } ds
                                                      ]
                                                      (delayed Ordering)
                                                    }
                                                    (lam
                                                      default_arg0
                                                      a
                                                      (let
                                                        (nonrec)
                                                        (termbind
                                                          (strict)
                                                          (vardecl
                                                            fail
                                                            (fun (all a (type) a) Ordering)
                                                          )
                                                          (lam
                                                            ds
                                                            (all a (type) a)
                                                            (force
                                                              [
                                                                [
                                                                  [
                                                                    {
                                                                      [
                                                                        {
                                                                          Extended_match
                                                                          a
                                                                        }
                                                                        ds
                                                                      ]
                                                                      (delayed Ordering)
                                                                    }
                                                                    (lam
                                                                      default_arg0
                                                                      a
                                                                      (delay
                                                                        (force
                                                                          [
                                                                            [
                                                                              [
                                                                                {
                                                                                  [
                                                                                    {
                                                                                      Extended_match
                                                                                      a
                                                                                    }
                                                                                    ds
                                                                                  ]
                                                                                  (delayed Ordering)
                                                                                }
                                                                                (lam
                                                                                  l
                                                                                  a
                                                                                  (delay
                                                                                    (force
                                                                                      [
                                                                                        [
                                                                                          [
                                                                                            {
                                                                                              [
                                                                                                {
                                                                                                  Extended_match
                                                                                                  a
                                                                                                }
                                                                                                ds
                                                                                              ]
                                                                                              (delayed Ordering)
                                                                                            }
                                                                                            (lam
                                                                                              r
                                                                                              a
                                                                                              (delay
                                                                                                [
                                                                                                  [
                                                                                                    [
                                                                                                      {
                                                                                                        compare
                                                                                                        a
                                                                                                      }
                                                                                                      dOrd
                                                                                                    ]
                                                                                                    l
                                                                                                  ]
                                                                                                  r
                                                                                                ]
                                                                                              )
                                                                                            )
                                                                                          ]
                                                                                          (delay
                                                                                            [
                                                                                              fail
                                                                                              (abs
                                                                                                e
                                                                                                (type)
                                                                                                (error
                                                                                                  e
                                                                                                )
                                                                                              )
                                                                                            ]
                                                                                          )
                                                                                        ]
                                                                                        (delay
                                                                                          [
                                                                                            fail
                                                                                            (abs
                                                                                              e
                                                                                              (type)
                                                                                              (error
                                                                                                e
                                                                                              )
                                                                                            )
                                                                                          ]
                                                                                        )
                                                                                      ]
                                                                                    )
                                                                                  )
                                                                                )
                                                                              ]
                                                                              (delay
                                                                                [
                                                                                  fail
                                                                                  (abs
                                                                                    e
                                                                                    (type)
                                                                                    (error
                                                                                      e
                                                                                    )
                                                                                  )
                                                                                ]
                                                                              )
                                                                            ]
                                                                            (delay
                                                                              GT
                                                                            )
                                                                          ]
                                                                        )
                                                                      )
                                                                    )
                                                                  ]
                                                                  (delay
                                                                    (force
                                                                      [
                                                                        [
                                                                          [
                                                                            {
                                                                              [
                                                                                {
                                                                                  Extended_match
                                                                                  a
                                                                                }
                                                                                ds
                                                                              ]
                                                                              (delayed Ordering)
                                                                            }
                                                                            (lam
                                                                              l
                                                                              a
                                                                              (delay
                                                                                (force
                                                                                  [
                                                                                    [
                                                                                      [
                                                                                        {
                                                                                          [
                                                                                            {
                                                                                              Extended_match
                                                                                              a
                                                                                            }
                                                                                            ds
                                                                                          ]
                                                                                          (delayed Ordering)
                                                                                        }
                                                                                        (lam
                                                                                          r
                                                                                          a
                                                                                          (delay
                                                                                            [
                                                                                              [
                                                                                                [
                                                                                                  {
                                                                                                    compare
                                                                                                    a
                                                                                                  }
                                                                                                  dOrd
                                                                                                ]
                                                                                                l
                                                                                              ]
                                                                                              r
                                                                                            ]
                                                                                          )
                                                                                        )
                                                                                      ]
                                                                                      (delay
                                                                                        [
                                                                                          fail
                                                                                          (abs
                                                                                            e
                                                                                            (type)
                                                                                            (error
                                                                                              e
                                                                                            )
                                                                                          )
                                                                                        ]
                                                                                      )
                                                                                    ]
                                                                                    (delay
                                                                                      [
                                                                                        fail
                                                                                        (abs
                                                                                          e
                                                                                          (type)
                                                                                          (error
                                                                                            e
                                                                                          )
                                                                                        )
                                                                                      ]
                                                                                    )
                                                                                  ]
                                                                                )
                                                                              )
                                                                            )
                                                                          ]
                                                                          (delay
                                                                            [
                                                                              fail
                                                                              (abs
                                                                                e
                                                                                (type)
                                                                                (error
                                                                                  e
                                                                                )
                                                                              )
                                                                            ]
                                                                          )
                                                                        ]
                                                                        (delay
                                                                          GT
                                                                        )
                                                                      ]
                                                                    )
                                                                  )
                                                                ]
                                                                (delay LT)
                                                              ]
                                                            )
                                                          )
                                                        )
                                                        (delay
                                                          (force
                                                            [
                                                              [
                                                                [
                                                                  {
                                                                    [
                                                                      {
                                                                        Extended_match
                                                                        a
                                                                      }
                                                                      ds
                                                                    ]
                                                                    (delayed Ordering)
                                                                  }
                                                                  (lam
                                                                    default_arg0
                                                                    a
                                                                    (delay
                                                                      [
                                                                        fail
                                                                        (abs
                                                                          e
                                                                          (type)
                                                                          (error
                                                                            e
                                                                          )
                                                                        )
                                                                      ]
                                                                    )
                                                                  )
                                                                ]
                                                                (delay
                                                                  [
                                                                    fail
                                                                    (abs
                                                                      e
                                                                      (type)
                                                                      (error e)
                                                                    )
                                                                  ]
                                                                )
                                                              ]
                                                              (delay
                                                                (force
                                                                  [
                                                                    [
                                                                      [
                                                                        {
                                                                          [
                                                                            {
                                                                              Extended_match
                                                                              a
                                                                            }
                                                                            ds
                                                                          ]
                                                                          (delayed Ordering)
                                                                        }
                                                                        (lam
                                                                          default_arg0
                                                                          a
                                                                          (delay
                                                                            [
                                                                              fail
                                                                              (abs
                                                                                e
                                                                                (type)
                                                                                (error
                                                                                  e
                                                                                )
                                                                              )
                                                                            ]
                                                                          )
                                                                        )
                                                                      ]
                                                                      (delay
                                                                        [
                                                                          fail
                                                                          (abs
                                                                            e
                                                                            (type)
                                                                            (error
                                                                              e
                                                                            )
                                                                          )
                                                                        ]
                                                                      )
                                                                    ]
                                                                    (delay EQ)
                                                                  ]
                                                                )
                                                              )
                                                            ]
                                                          )
                                                        )
                                                      )
                                                    )
                                                  ]
                                                  (delay GT)
                                                ]
                                                (delay
                                                  (force
                                                    [
                                                      [
                                                        [
                                                          {
                                                            [
                                                              {
                                                                Extended_match a
                                                              }
                                                              ds
                                                            ]
                                                            (delayed Ordering)
                                                          }
                                                          (lam
                                                            default_arg0
                                                            a
                                                            (delay
                                                              [
                                                                fail
                                                                (abs
                                                                  e
                                                                  (type)
                                                                  (error e)
                                                                )
                                                              ]
                                                            )
                                                          )
                                                        ]
                                                        (delay
                                                          [
                                                            fail
                                                            (abs
                                                              e (type) (error e)
                                                            )
                                                          ]
                                                        )
                                                      ]
                                                      (delay
                                                        (force
                                                          [
                                                            [
                                                              [
                                                                {
                                                                  [
                                                                    {
                                                                      Extended_match
                                                                      a
                                                                    }
                                                                    ds
                                                                  ]
                                                                  (delayed Ordering)
                                                                }
                                                                (lam
                                                                  default_arg0
                                                                  a
                                                                  (delay
                                                                    [
                                                                      fail
                                                                      (abs
                                                                        e
                                                                        (type)
                                                                        (error e
                                                                        )
                                                                      )
                                                                    ]
                                                                  )
                                                                )
                                                              ]
                                                              (delay
                                                                [
                                                                  fail
                                                                  (abs
                                                                    e
                                                                    (type)
                                                                    (error e)
                                                                  )
                                                                ]
                                                              )
                                                            ]
                                                            (delay EQ)
                                                          ]
                                                        )
                                                      )
                                                    ]
                                                  )
                                                )
                                              ]
                                            )
                                          )
                                        )
                                      )
                                    ]
                                    (delay
                                      (force
                                        [
                                          [
                                            [
                                              {
                                                [ { Extended_match a } ds ]
                                                (delayed Ordering)
                                              }
                                              (lam default_arg0 a (delay LT))
                                            ]
                                            (delay EQ)
                                          ]
                                          (delay LT)
                                        ]
                                      )
                                    )
                                  ]
                                  (delay
                                    (force
                                      [
                                        [
                                          [
                                            {
                                              [ { Extended_match a } ds ]
                                              (delayed Ordering)
                                            }
                                            (lam
                                              default_arg0
                                              a
                                              (let
                                                (nonrec)
                                                (termbind
                                                  (strict)
                                                  (vardecl
                                                    fail
                                                    (fun (all a (type) a) Ordering)
                                                  )
                                                  (lam
                                                    ds
                                                    (all a (type) a)
                                                    (force
                                                      [
                                                        [
                                                          [
                                                            {
                                                              [
                                                                {
                                                                  Extended_match
                                                                  a
                                                                }
                                                                ds
                                                              ]
                                                              (delayed Ordering)
                                                            }
                                                            (lam
                                                              default_arg0
                                                              a
                                                              (delay
                                                                (force
                                                                  [
                                                                    [
                                                                      [
                                                                        {
                                                                          [
                                                                            {
                                                                              Extended_match
                                                                              a
                                                                            }
                                                                            ds
                                                                          ]
                                                                          (delayed Ordering)
                                                                        }
                                                                        (lam
                                                                          l
                                                                          a
                                                                          (delay
                                                                            (force
                                                                              [
                                                                                [
                                                                                  [
                                                                                    {
                                                                                      [
                                                                                        {
                                                                                          Extended_match
                                                                                          a
                                                                                        }
                                                                                        ds
                                                                                      ]
                                                                                      (delayed Ordering)
                                                                                    }
                                                                                    (lam
                                                                                      r
                                                                                      a
                                                                                      (delay
                                                                                        [
                                                                                          [
                                                                                            [
                                                                                              {
                                                                                                compare
                                                                                                a
                                                                                              }
                                                                                              dOrd
                                                                                            ]
                                                                                            l
                                                                                          ]
                                                                                          r
                                                                                        ]
                                                                                      )
                                                                                    )
                                                                                  ]
                                                                                  (delay
                                                                                    [
                                                                                      fail
                                                                                      (abs
                                                                                        e
                                                                                        (type)
                                                                                        (error
                                                                                          e
                                                                                        )
                                                                                      )
                                                                                    ]
                                                                                  )
                                                                                ]
                                                                                (delay
                                                                                  [
                                                                                    fail
                                                                                    (abs
                                                                                      e
                                                                                      (type)
                                                                                      (error
                                                                                        e
                                                                                      )
                                                                                    )
                                                                                  ]
                                                                                )
                                                                              ]
                                                                            )
                                                                          )
                                                                        )
                                                                      ]
                                                                      (delay
                                                                        [
                                                                          fail
                                                                          (abs
                                                                            e
                                                                            (type)
                                                                            (error
                                                                              e
                                                                            )
                                                                          )
                                                                        ]
                                                                      )
                                                                    ]
                                                                    (delay GT)
                                                                  ]
                                                                )
                                                              )
                                                            )
                                                          ]
                                                          (delay
                                                            (force
                                                              [
                                                                [
                                                                  [
                                                                    {
                                                                      [
                                                                        {
                                                                          Extended_match
                                                                          a
                                                                        }
                                                                        ds
                                                                      ]
                                                                      (delayed Ordering)
                                                                    }
                                                                    (lam
                                                                      l
                                                                      a
                                                                      (delay
                                                                        (force
                                                                          [
                                                                            [
                                                                              [
                                                                                {
                                                                                  [
                                                                                    {
                                                                                      Extended_match
                                                                                      a
                                                                                    }
                                                                                    ds
                                                                                  ]
                                                                                  (delayed Ordering)
                                                                                }
                                                                                (lam
                                                                                  r
                                                                                  a
                                                                                  (delay
                                                                                    [
                                                                                      [
                                                                                        [
                                                                                          {
                                                                                            compare
                                                                                            a
                                                                                          }
                                                                                          dOrd
                                                                                        ]
                                                                                        l
                                                                                      ]
                                                                                      r
                                                                                    ]
                                                                                  )
                                                                                )
                                                                              ]
                                                                              (delay
                                                                                [
                                                                                  fail
                                                                                  (abs
                                                                                    e
                                                                                    (type)
                                                                                    (error
                                                                                      e
                                                                                    )
                                                                                  )
                                                                                ]
                                                                              )
                                                                            ]
                                                                            (delay
                                                                              [
                                                                                fail
                                                                                (abs
                                                                                  e
                                                                                  (type)
                                                                                  (error
                                                                                    e
                                                                                  )
                                                                                )
                                                                              ]
                                                                            )
                                                                          ]
                                                                        )
                                                                      )
                                                                    )
                                                                  ]
                                                                  (delay
                                                                    [
                                                                      fail
                                                                      (abs
                                                                        e
                                                                        (type)
                                                                        (error e
                                                                        )
                                                                      )
                                                                    ]
                                                                  )
                                                                ]
                                                                (delay GT)
                                                              ]
                                                            )
                                                          )
                                                        ]
                                                        (delay LT)
                                                      ]
                                                    )
                                                  )
                                                )
                                                (delay
                                                  (force
                                                    [
                                                      [
                                                        [
                                                          {
                                                            [
                                                              {
                                                                Extended_match a
                                                              }
                                                              ds
                                                            ]
                                                            (delayed Ordering)
                                                          }
                                                          (lam
                                                            default_arg0
                                                            a
                                                            (delay
                                                              [
                                                                fail
                                                                (abs
                                                                  e
                                                                  (type)
                                                                  (error e)
                                                                )
                                                              ]
                                                            )
                                                          )
                                                        ]
                                                        (delay
                                                          [
                                                            fail
                                                            (abs
                                                              e (type) (error e)
                                                            )
                                                          ]
                                                        )
                                                      ]
                                                      (delay
                                                        (force
                                                          [
                                                            [
                                                              [
                                                                {
                                                                  [
                                                                    {
                                                                      Extended_match
                                                                      a
                                                                    }
                                                                    ds
                                                                  ]
                                                                  (delayed Ordering)
                                                                }
                                                                (lam
                                                                  default_arg0
                                                                  a
                                                                  (delay
                                                                    [
                                                                      fail
                                                                      (abs
                                                                        e
                                                                        (type)
                                                                        (error e
                                                                        )
                                                                      )
                                                                    ]
                                                                  )
                                                                )
                                                              ]
                                                              (delay
                                                                [
                                                                  fail
                                                                  (abs
                                                                    e
                                                                    (type)
                                                                    (error e)
                                                                  )
                                                                ]
                                                              )
                                                            ]
                                                            (delay EQ)
                                                          ]
                                                        )
                                                      )
                                                    ]
                                                  )
                                                )
                                              )
                                            )
                                          ]
                                          (delay GT)
                                        ]
                                        (delay
                                          (force
                                            [
                                              [
                                                [
                                                  {
                                                    [ { Extended_match a } ds ]
                                                    (delayed Ordering)
                                                  }
                                                  (lam
                                                    default_arg0
                                                    a
                                                    (delay
                                                      [
                                                        fail
                                                        (abs e (type) (error e))
                                                      ]
                                                    )
                                                  )
                                                ]
                                                (delay
                                                  [
                                                    fail
                                                    (abs e (type) (error e))
                                                  ]
                                                )
                                              ]
                                              (delay
                                                (force
                                                  [
                                                    [
                                                      [
                                                        {
                                                          [
                                                            { Extended_match a }
                                                            ds
                                                          ]
                                                          (delayed Ordering)
                                                        }
                                                        (lam
                                                          default_arg0
                                                          a
                                                          (delay
                                                            [
                                                              fail
                                                              (abs
                                                                e
                                                                (type)
                                                                (error e)
                                                              )
                                                            ]
                                                          )
                                                        )
                                                      ]
                                                      (delay
                                                        [
                                                          fail
                                                          (abs
                                                            e (type) (error e)
                                                          )
                                                        ]
                                                      )
                                                    ]
                                                    (delay EQ)
                                                  ]
                                                )
                                              )
                                            ]
                                          )
                                        )
                                      ]
                                    )
                                  )
                                ]
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      fOrdUpperBound0_c
                      (all a (type) (fun [Ord a] (fun [UpperBound a] (fun [UpperBound a] Bool))))
                    )
                    (abs
                      a
                      (type)
                      (lam
                        dOrd
                        [Ord a]
                        (lam
                          x
                          [UpperBound a]
                          (lam
                            y
                            [UpperBound a]
                            [
                              { [ { UpperBound_match a } x ] Bool }
                              (lam
                                v
                                [Extended a]
                                (lam
                                  in
                                  Bool
                                  [
                                    { [ { UpperBound_match a } y ] Bool }
                                    (lam
                                      v
                                      [Extended a]
                                      (lam
                                        in
                                        Bool
                                        (force
                                          [
                                            [
                                              [
                                                {
                                                  [
                                                    Ordering_match
                                                    [
                                                      [
                                                        [
                                                          { hull_ccompare a }
                                                          dOrd
                                                        ]
                                                        v
                                                      ]
                                                      v
                                                    ]
                                                  ]
                                                  (delayed Bool)
                                                }
                                                (delay
                                                  (force
                                                    [
                                                      [
                                                        {
                                                          [ Bool_match in ]
                                                          (delayed Bool)
                                                        }
                                                        (delay in)
                                                      ]
                                                      (delay True)
                                                    ]
                                                  )
                                                )
                                              ]
                                              (delay False)
                                            ]
                                            (delay True)
                                          ]
                                        )
                                      )
                                    )
                                  ]
                                )
                              )
                            ]
                          )
                        )
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      contains
                      (all a (type) (fun [Ord a] (fun [Interval a] (fun [Interval a] Bool))))
                    )
                    (abs
                      a
                      (type)
                      (lam
                        dOrd
                        [Ord a]
                        (lam
                          ds
                          [Interval a]
                          (lam
                            ds
                            [Interval a]
                            [
                              { [ { Interval_match a } ds ] Bool }
                              (lam
                                l
                                [LowerBound a]
                                (lam
                                  h
                                  [UpperBound a]
                                  [
                                    { [ { Interval_match a } ds ] Bool }
                                    (lam
                                      l
                                      [LowerBound a]
                                      (lam
                                        h
                                        [UpperBound a]
                                        [
                                          { [ { LowerBound_match a } l ] Bool }
                                          (lam
                                            v
                                            [Extended a]
                                            (lam
                                              in
                                              Bool
                                              [
                                                {
                                                  [ { LowerBound_match a } l ]
                                                  Bool
                                                }
                                                (lam
                                                  v
                                                  [Extended a]
                                                  (lam
                                                    in
                                                    Bool
                                                    (force
                                                      [
                                                        [
                                                          [
                                                            {
                                                              [
                                                                Ordering_match
                                                                [
                                                                  [
                                                                    [
                                                                      {
                                                                        hull_ccompare
                                                                        a
                                                                      }
                                                                      dOrd
                                                                    ]
                                                                    v
                                                                  ]
                                                                  v
                                                                ]
                                                              ]
                                                              (delayed Bool)
                                                            }
                                                            (delay
                                                              (force
                                                                [
                                                                  [
                                                                    {
                                                                      [
                                                                        Bool_match
                                                                        in
                                                                      ]
                                                                      (delayed Bool)
                                                                    }
                                                                    (delay
                                                                      (force
                                                                        [
                                                                          [
                                                                            {
                                                                              [
                                                                                Bool_match
                                                                                in
                                                                              ]
                                                                              (delayed Bool)
                                                                            }
                                                                            (delay
                                                                              [
                                                                                [
                                                                                  [
                                                                                    {
                                                                                      fOrdUpperBound0_c
                                                                                      a
                                                                                    }
                                                                                    dOrd
                                                                                  ]
                                                                                  h
                                                                                ]
                                                                                h
                                                                              ]
                                                                            )
                                                                          ]
                                                                          (delay
                                                                            False
                                                                          )
                                                                        ]
                                                                      )
                                                                    )
                                                                  ]
                                                                  (delay
                                                                    [
                                                                      [
                                                                        [
                                                                          {
                                                                            fOrdUpperBound0_c
                                                                            a
                                                                          }
                                                                          dOrd
                                                                        ]
                                                                        h
                                                                      ]
                                                                      h
                                                                    ]
                                                                  )
                                                                ]
                                                              )
                                                            )
                                                          ]
                                                          (delay False)
                                                        ]
                                                        (delay
                                                          [
                                                            [
                                                              [
                                                                {
                                                                  fOrdUpperBound0_c
                                                                  a
                                                                }
                                                                dOrd
                                                              ]
                                                              h
                                                            ]
                                                            h
                                                          ]
                                                        )
                                                      ]
                                                    )
                                                  )
                                                )
                                              ]
                                            )
                                          )
                                        ]
                                      )
                                    )
                                  ]
                                )
                              )
                            ]
                          )
                        )
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl equalsData (fun (con data) (fun (con data) Bool)))
                    (lam
                      d
                      (con data)
                      (lam
                        d
                        (con data)
                        [
                          [
                            [
                              { (builtin ifThenElse) Bool }
                              [ [ (builtin equalsData) d ] d ]
                            ]
                            True
                          ]
                          False
                        ]
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      findDatum
                      (fun (con bytestring) (fun TxInfo [Maybe (con data)]))
                    )
                    (lam
                      dsh
                      (con bytestring)
                      (lam
                        ds
                        TxInfo
                        [
                          { [ TxInfo_match ds ] [Maybe (con data)] }
                          (lam
                            ds
                            [List TxInInfo]
                            (lam
                              ds
                              [List TxOut]
                              (lam
                                ds
                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                (lam
                                  ds
                                  [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                  (lam
                                    ds
                                    [List DCert]
                                    (lam
                                      ds
                                      [List [[Tuple2 StakingCredential] (con integer)]]
                                      (lam
                                        ds
                                        [Interval (con integer)]
                                        (lam
                                          ds
                                          [List (con bytestring)]
                                          (lam
                                            ds
                                            [List [[Tuple2 (con bytestring)] (con data)]]
                                            (lam
                                              ds
                                              (con bytestring)
                                              (force
                                                [
                                                  [
                                                    {
                                                      [
                                                        {
                                                          Maybe_match
                                                          [[Tuple2 (con bytestring)] (con data)]
                                                        }
                                                        [
                                                          [
                                                            [
                                                              {
                                                                {
                                                                  fFoldableNil_cfoldMap
                                                                  [(lam a (type) [Maybe a]) [[Tuple2 (con bytestring)] (con data)]]
                                                                }
                                                                [[Tuple2 (con bytestring)] (con data)]
                                                              }
                                                              {
                                                                fMonoidFirst
                                                                [[Tuple2 (con bytestring)] (con data)]
                                                              }
                                                            ]
                                                            (lam
                                                              x
                                                              [[Tuple2 (con bytestring)] (con data)]
                                                              [
                                                                {
                                                                  [
                                                                    {
                                                                      {
                                                                        Tuple2_match
                                                                        (con bytestring)
                                                                      }
                                                                      (con data)
                                                                    }
                                                                    x
                                                                  ]
                                                                  [Maybe [[Tuple2 (con bytestring)] (con data)]]
                                                                }
                                                                (lam
                                                                  dsh
                                                                  (con bytestring)
                                                                  (lam
                                                                    ds
                                                                    (con data)
                                                                    (force
                                                                      [
                                                                        [
                                                                          {
                                                                            [
                                                                              Bool_match
                                                                              [
                                                                                [
                                                                                  [
                                                                                    {
                                                                                      (builtin
                                                                                        ifThenElse
                                                                                      )
                                                                                      Bool
                                                                                    }
                                                                                    [
                                                                                      [
                                                                                        (builtin
                                                                                          equalsByteString
                                                                                        )
                                                                                        dsh
                                                                                      ]
                                                                                      dsh
                                                                                    ]
                                                                                  ]
                                                                                  True
                                                                                ]
                                                                                False
                                                                              ]
                                                                            ]
                                                                            (delayed [Maybe [[Tuple2 (con bytestring)] (con data)]])
                                                                          }
                                                                          (delay
                                                                            [
                                                                              {
                                                                                Just
                                                                                [[Tuple2 (con bytestring)] (con data)]
                                                                              }
                                                                              x
                                                                            ]
                                                                          )
                                                                        ]
                                                                        (delay
                                                                          {
                                                                            Nothing
                                                                            [[Tuple2 (con bytestring)] (con data)]
                                                                          }
                                                                        )
                                                                      ]
                                                                    )
                                                                  )
                                                                )
                                                              ]
                                                            )
                                                          ]
                                                          ds
                                                        ]
                                                      ]
                                                      (delayed [Maybe (con data)])
                                                    }
                                                    (lam
                                                      a
                                                      [[Tuple2 (con bytestring)] (con data)]
                                                      (delay
                                                        [
                                                          { Just (con data) }
                                                          [
                                                            {
                                                              [
                                                                {
                                                                  {
                                                                    Tuple2_match
                                                                    (con bytestring)
                                                                  }
                                                                  (con data)
                                                                }
                                                                a
                                                              ]
                                                              (con data)
                                                            }
                                                            (lam
                                                              ds
                                                              (con bytestring)
                                                              (lam
                                                                b (con data) b
                                                              )
                                                            )
                                                          ]
                                                        ]
                                                      )
                                                    )
                                                  ]
                                                  (delay { Nothing (con data) })
                                                ]
                                              )
                                            )
                                          )
                                        )
                                      )
                                    )
                                  )
                                )
                              )
                            )
                          )
                        ]
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      findTxInByTxOutRef
                      (fun TxOutRef (fun TxInfo [Maybe TxInInfo]))
                    )
                    (lam
                      outRef
                      TxOutRef
                      (lam
                        ds
                        TxInfo
                        [
                          { [ TxInfo_match ds ] [Maybe TxInInfo] }
                          (lam
                            ds
                            [List TxInInfo]
                            (lam
                              ds
                              [List TxOut]
                              (lam
                                ds
                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                (lam
                                  ds
                                  [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                  (lam
                                    ds
                                    [List DCert]
                                    (lam
                                      ds
                                      [List [[Tuple2 StakingCredential] (con integer)]]
                                      (lam
                                        ds
                                        [Interval (con integer)]
                                        (lam
                                          ds
                                          [List (con bytestring)]
                                          (lam
                                            ds
                                            [List [[Tuple2 (con bytestring)] (con data)]]
                                            (lam
                                              ds
                                              (con bytestring)
                                              [
                                                [
                                                  [
                                                    {
                                                      {
                                                        fFoldableNil_cfoldMap
                                                        [(lam a (type) [Maybe a]) TxInInfo]
                                                      }
                                                      TxInInfo
                                                    }
                                                    { fMonoidFirst TxInInfo }
                                                  ]
                                                  (lam
                                                    x
                                                    TxInInfo
                                                    [
                                                      {
                                                        [ TxInInfo_match x ]
                                                        [Maybe TxInInfo]
                                                      }
                                                      (lam
                                                        ds
                                                        TxOutRef
                                                        (lam
                                                          ds
                                                          TxOut
                                                          (force
                                                            [
                                                              [
                                                                {
                                                                  [
                                                                    Bool_match
                                                                    [
                                                                      [
                                                                        fEqTxOutRef_c
                                                                        ds
                                                                      ]
                                                                      outRef
                                                                    ]
                                                                  ]
                                                                  (delayed [Maybe TxInInfo])
                                                                }
                                                                (delay
                                                                  [
                                                                    {
                                                                      Just
                                                                      TxInInfo
                                                                    }
                                                                    x
                                                                  ]
                                                                )
                                                              ]
                                                              (delay
                                                                {
                                                                  Nothing
                                                                  TxInInfo
                                                                }
                                                              )
                                                            ]
                                                          )
                                                        )
                                                      )
                                                    ]
                                                  )
                                                ]
                                                ds
                                              ]
                                            )
                                          )
                                        )
                                      )
                                    )
                                  )
                                )
                              )
                            )
                          )
                        ]
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      snd (all a (type) (all b (type) (fun [[Tuple2 a] b] b)))
                    )
                    (abs
                      a
                      (type)
                      (abs
                        b
                        (type)
                        (lam
                          ds
                          [[Tuple2 a] b]
                          [
                            { [ { { Tuple2_match a } b } ds ] b }
                            (lam ds a (lam b b b))
                          ]
                        )
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl txSignedBy (fun TxInfo (fun (con bytestring) Bool))
                    )
                    (lam
                      ds
                      TxInfo
                      (lam
                        k
                        (con bytestring)
                        [
                          { [ TxInfo_match ds ] Bool }
                          (lam
                            ds
                            [List TxInInfo]
                            (lam
                              ds
                              [List TxOut]
                              (lam
                                ds
                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                (lam
                                  ds
                                  [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                  (lam
                                    ds
                                    [List DCert]
                                    (lam
                                      ds
                                      [List [[Tuple2 StakingCredential] (con integer)]]
                                      (lam
                                        ds
                                        [Interval (con integer)]
                                        (lam
                                          ds
                                          [List (con bytestring)]
                                          (lam
                                            ds
                                            [List [[Tuple2 (con bytestring)] (con data)]]
                                            (lam
                                              ds
                                              (con bytestring)
                                              (force
                                                [
                                                  [
                                                    {
                                                      [
                                                        {
                                                          Maybe_match
                                                          (con bytestring)
                                                        }
                                                        [
                                                          [
                                                            [
                                                              {
                                                                {
                                                                  fFoldableNil_cfoldMap
                                                                  [(lam a (type) [Maybe a]) (con bytestring)]
                                                                }
                                                                (con bytestring)
                                                              }
                                                              {
                                                                fMonoidFirst
                                                                (con bytestring)
                                                              }
                                                            ]
                                                            (lam
                                                              x
                                                              (con bytestring)
                                                              (force
                                                                [
                                                                  [
                                                                    {
                                                                      [
                                                                        Bool_match
                                                                        [
                                                                          [
                                                                            [
                                                                              {
                                                                                (builtin
                                                                                  ifThenElse
                                                                                )
                                                                                Bool
                                                                              }
                                                                              [
                                                                                [
                                                                                  (builtin
                                                                                    equalsByteString
                                                                                  )
                                                                                  k
                                                                                ]
                                                                                x
                                                                              ]
                                                                            ]
                                                                            True
                                                                          ]
                                                                          False
                                                                        ]
                                                                      ]
                                                                      (delayed [Maybe (con bytestring)])
                                                                    }
                                                                    (delay
                                                                      [
                                                                        {
                                                                          Just
                                                                          (con bytestring)
                                                                        }
                                                                        x
                                                                      ]
                                                                    )
                                                                  ]
                                                                  (delay
                                                                    {
                                                                      Nothing
                                                                      (con bytestring)
                                                                    }
                                                                  )
                                                                ]
                                                              )
                                                            )
                                                          ]
                                                          ds
                                                        ]
                                                      ]
                                                      (delayed Bool)
                                                    }
                                                    (lam
                                                      ds
                                                      (con bytestring)
                                                      (delay True)
                                                    )
                                                  ]
                                                  (delay False)
                                                ]
                                              )
                                            )
                                          )
                                        )
                                      )
                                    )
                                  )
                                )
                              )
                            )
                          )
                        ]
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      valueOf
                      (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun (con bytestring) (fun (con bytestring) (con integer))))
                    )
                    (lam
                      ds
                      [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                      (lam
                        cur
                        (con bytestring)
                        (lam
                          tn
                          (con bytestring)
                          (let
                            (nonrec)
                            (termbind
                              (strict)
                              (vardecl
                                j
                                (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)] (con integer))
                              )
                              (lam
                                i
                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]
                                (let
                                  (rec)
                                  (termbind
                                    (strict)
                                    (vardecl
                                      go
                                      (fun [List [[Tuple2 (con bytestring)] (con integer)]] (con integer))
                                    )
                                    (lam
                                      ds
                                      [List [[Tuple2 (con bytestring)] (con integer)]]
                                      [
                                        [
                                          {
                                            [
                                              {
                                                Nil_match
                                                [[Tuple2 (con bytestring)] (con integer)]
                                              }
                                              ds
                                            ]
                                            (con integer)
                                          }
                                          (con integer 0)
                                        ]
                                        (lam
                                          ds
                                          [[Tuple2 (con bytestring)] (con integer)]
                                          (lam
                                            xs
                                            [List [[Tuple2 (con bytestring)] (con integer)]]
                                            [
                                              {
                                                [
                                                  {
                                                    {
                                                      Tuple2_match
                                                      (con bytestring)
                                                    }
                                                    (con integer)
                                                  }
                                                  ds
                                                ]
                                                (con integer)
                                              }
                                              (lam
                                                c
                                                (con bytestring)
                                                (lam
                                                  i
                                                  (con integer)
                                                  (force
                                                    [
                                                      [
                                                        {
                                                          [
                                                            Bool_match
                                                            [
                                                              [
                                                                [
                                                                  {
                                                                    (builtin
                                                                      ifThenElse
                                                                    )
                                                                    Bool
                                                                  }
                                                                  [
                                                                    [
                                                                      (builtin
                                                                        equalsByteString
                                                                      )
                                                                      c
                                                                    ]
                                                                    tn
                                                                  ]
                                                                ]
                                                                True
                                                              ]
                                                              False
                                                            ]
                                                          ]
                                                          (delayed (con integer))
                                                        }
                                                        (delay i)
                                                      ]
                                                      (delay [ go xs ])
                                                    ]
                                                  )
                                                )
                                              )
                                            ]
                                          )
                                        )
                                      ]
                                    )
                                  )
                                  [ go i ]
                                )
                              )
                            )
                            (let
                              (rec)
                              (termbind
                                (strict)
                                (vardecl
                                  go
                                  (fun [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]] (con integer))
                                )
                                (lam
                                  ds
                                  [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                  [
                                    [
                                      {
                                        [
                                          {
                                            Nil_match
                                            [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                          }
                                          ds
                                        ]
                                        (con integer)
                                      }
                                      (con integer 0)
                                    ]
                                    (lam
                                      ds
                                      [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                      (lam
                                        xs
                                        [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                        [
                                          {
                                            [
                                              {
                                                {
                                                  Tuple2_match (con bytestring)
                                                }
                                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]
                                              }
                                              ds
                                            ]
                                            (con integer)
                                          }
                                          (lam
                                            c
                                            (con bytestring)
                                            (lam
                                              i
                                              [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]
                                              (force
                                                [
                                                  [
                                                    {
                                                      [
                                                        Bool_match
                                                        [
                                                          [
                                                            [
                                                              {
                                                                (builtin
                                                                  ifThenElse
                                                                )
                                                                Bool
                                                              }
                                                              [
                                                                [
                                                                  (builtin
                                                                    equalsByteString
                                                                  )
                                                                  c
                                                                ]
                                                                cur
                                                              ]
                                                            ]
                                                            True
                                                          ]
                                                          False
                                                        ]
                                                      ]
                                                      (delayed (con integer))
                                                    }
                                                    (delay [ j i ])
                                                  ]
                                                  (delay [ go xs ])
                                                ]
                                              )
                                            )
                                          )
                                        ]
                                      )
                                    )
                                  ]
                                )
                              )
                              [ go ds ]
                            )
                          )
                        )
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      foldr
                      (all a (type) (all b (type) (fun (fun a (fun b b)) (fun b (fun [List a] b)))))
                    )
                    (abs
                      a
                      (type)
                      (abs
                        b
                        (type)
                        (lam
                          k
                          (fun a (fun b b))
                          (lam
                            z
                            b
                            (let
                              (rec)
                              (termbind
                                (strict)
                                (vardecl go (fun [List a] b))
                                (lam
                                  ds
                                  [List a]
                                  (force
                                    [
                                      [
                                        { [ { Nil_match a } ds ] (delayed b) }
                                        (delay z)
                                      ]
                                      (lam
                                        y
                                        a
                                        (lam
                                          ys
                                          [List a]
                                          (delay [ [ k y ] [ go ys ] ])
                                        )
                                      )
                                    ]
                                  )
                                )
                              )
                              go
                            )
                          )
                        )
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      pubKeyOutputsAt
                      (fun (con bytestring) (fun TxInfo [List [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]))
                    )
                    (lam
                      pk
                      (con bytestring)
                      (lam
                        p
                        TxInfo
                        [
                          {
                            [ TxInfo_match p ]
                            [List [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                          }
                          (lam
                            ds
                            [List TxInInfo]
                            (lam
                              ds
                              [List TxOut]
                              (lam
                                ds
                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                (lam
                                  ds
                                  [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                  (lam
                                    ds
                                    [List DCert]
                                    (lam
                                      ds
                                      [List [[Tuple2 StakingCredential] (con integer)]]
                                      (lam
                                        ds
                                        [Interval (con integer)]
                                        (lam
                                          ds
                                          [List (con bytestring)]
                                          (lam
                                            ds
                                            [List [[Tuple2 (con bytestring)] (con data)]]
                                            (lam
                                              ds
                                              (con bytestring)
                                              [
                                                [
                                                  [
                                                    {
                                                      { foldr TxOut }
                                                      [List [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                    }
                                                    (lam
                                                      e
                                                      TxOut
                                                      (lam
                                                        xs
                                                        [List [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                        [
                                                          {
                                                            [ TxOut_match e ]
                                                            [List [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                          }
                                                          (lam
                                                            ds
                                                            Address
                                                            (lam
                                                              ds
                                                              [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                              (lam
                                                                ds
                                                                [Maybe (con bytestring)]
                                                                [
                                                                  {
                                                                    [
                                                                      Address_match
                                                                      ds
                                                                    ]
                                                                    [List [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                                  }
                                                                  (lam
                                                                    ds
                                                                    Credential
                                                                    (lam
                                                                      ds
                                                                      [Maybe StakingCredential]
                                                                      [
                                                                        [
                                                                          {
                                                                            [
                                                                              Credential_match
                                                                              ds
                                                                            ]
                                                                            [List [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                                          }
                                                                          (lam
                                                                            pk
                                                                            (con bytestring)
                                                                            (force
                                                                              [
                                                                                [
                                                                                  {
                                                                                    [
                                                                                      Bool_match
                                                                                      [
                                                                                        [
                                                                                          [
                                                                                            {
                                                                                              (builtin
                                                                                                ifThenElse
                                                                                              )
                                                                                              Bool
                                                                                            }
                                                                                            [
                                                                                              [
                                                                                                (builtin
                                                                                                  equalsByteString
                                                                                                )
                                                                                                pk
                                                                                              ]
                                                                                              pk
                                                                                            ]
                                                                                          ]
                                                                                          True
                                                                                        ]
                                                                                        False
                                                                                      ]
                                                                                    ]
                                                                                    (delayed [List [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]])
                                                                                  }
                                                                                  (delay
                                                                                    [
                                                                                      [
                                                                                        {
                                                                                          Cons
                                                                                          [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                        }
                                                                                        ds
                                                                                      ]
                                                                                      xs
                                                                                    ]
                                                                                  )
                                                                                ]
                                                                                (delay
                                                                                  xs
                                                                                )
                                                                              ]
                                                                            )
                                                                          )
                                                                        ]
                                                                        (lam
                                                                          ipv
                                                                          (con bytestring)
                                                                          xs
                                                                        )
                                                                      ]
                                                                    )
                                                                  )
                                                                ]
                                                              )
                                                            )
                                                          )
                                                        ]
                                                      )
                                                    )
                                                  ]
                                                  {
                                                    Nil
                                                    [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                  }
                                                ]
                                                ds
                                              ]
                                            )
                                          )
                                        )
                                      )
                                    )
                                  )
                                )
                              )
                            )
                          )
                        ]
                      )
                    )
                  )
                  (termbind
                    (nonstrict)
                    (vardecl
                      fMonoidValue_c
                      (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]))
                    )
                    [ unionWith addInteger ]
                  )
                  (termbind
                    (strict)
                    (vardecl
                      valuePaidTo
                      (fun TxInfo (fun (con bytestring) [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]))
                    )
                    (lam
                      ptx
                      TxInfo
                      (lam
                        pkh
                        (con bytestring)
                        [
                          [
                            [
                              {
                                {
                                  foldr
                                  [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                }
                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                              }
                              fMonoidValue_c
                            ]
                            {
                              Nil
                              [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                            }
                          ]
                          [ [ pubKeyOutputsAt pkh ] ptx ]
                        ]
                      )
                    )
                  )
                  (termbind
                    (nonstrict)
                    (vardecl
                      fMonoidValue
                      [Monoid [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                    )
                    [
                      [
                        {
                          CConsMonoid
                          [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                        }
                        fMonoidValue_c
                      ]
                      {
                        Nil
                        [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                      }
                    ]
                  )
                  (termbind
                    (strict)
                    (vardecl
                      txOutValue
                      (fun TxOut [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]])
                    )
                    (lam
                      ds
                      TxOut
                      [
                        {
                          [ TxOut_match ds ]
                          [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                        }
                        (lam
                          ds
                          Address
                          (lam
                            ds
                            [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                            (lam ds [Maybe (con bytestring)] ds)
                          )
                        )
                      ]
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      valueProduced
                      (fun TxInfo [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]])
                    )
                    (lam
                      x
                      TxInfo
                      [
                        {
                          [ TxInfo_match x ]
                          [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                        }
                        (lam
                          ds
                          [List TxInInfo]
                          (lam
                            ds
                            [List TxOut]
                            (lam
                              ds
                              [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                              (lam
                                ds
                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                (lam
                                  ds
                                  [List DCert]
                                  (lam
                                    ds
                                    [List [[Tuple2 StakingCredential] (con integer)]]
                                    (lam
                                      ds
                                      [Interval (con integer)]
                                      (lam
                                        ds
                                        [List (con bytestring)]
                                        (lam
                                          ds
                                          [List [[Tuple2 (con bytestring)] (con data)]]
                                          (lam
                                            ds
                                            (con bytestring)
                                            [
                                              [
                                                [
                                                  {
                                                    {
                                                      fFoldableNil_cfoldMap
                                                      [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                    }
                                                    TxOut
                                                  }
                                                  fMonoidValue
                                                ]
                                                txOutValue
                                              ]
                                              ds
                                            ]
                                          )
                                        )
                                      )
                                    )
                                  )
                                )
                              )
                            )
                          )
                        )
                      ]
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      checkTxConstraint
                      (fun ScriptContext (fun TxConstraint Bool))
                    )
                    (lam
                      ds
                      ScriptContext
                      [
                        { [ ScriptContext_match ds ] (fun TxConstraint Bool) }
                        (lam
                          ds
                          TxInfo
                          (lam
                            ds
                            ScriptPurpose
                            (lam
                              ds
                              TxConstraint
                              [
                                [
                                  [
                                    [
                                      [
                                        [
                                          [
                                            [
                                              [
                                                [
                                                  [
                                                    {
                                                      [ TxConstraint_match ds ]
                                                      Bool
                                                    }
                                                    (lam
                                                      pubKey
                                                      (con bytestring)
                                                      (force
                                                        [
                                                          [
                                                            {
                                                              [
                                                                Bool_match
                                                                [
                                                                  [
                                                                    txSignedBy
                                                                    ds
                                                                  ]
                                                                  pubKey
                                                                ]
                                                              ]
                                                              (delayed Bool)
                                                            }
                                                            (delay True)
                                                          ]
                                                          (delay
                                                            [
                                                              [
                                                                {
                                                                  (builtin
                                                                    chooseUnit
                                                                  )
                                                                  Bool
                                                                }
                                                                [
                                                                  (builtin trace
                                                                  )
                                                                  (con
                                                                    string
                                                                      "Missing signature"
                                                                  )
                                                                ]
                                                              ]
                                                              False
                                                            ]
                                                          )
                                                        ]
                                                      )
                                                    )
                                                  ]
                                                  (lam
                                                    dvh
                                                    (con bytestring)
                                                    (lam
                                                      dv
                                                      (con data)
                                                      (let
                                                        (nonrec)
                                                        (termbind
                                                          (nonstrict)
                                                          (vardecl j Bool)
                                                          [
                                                            [
                                                              {
                                                                (builtin
                                                                  chooseUnit
                                                                )
                                                                Bool
                                                              }
                                                              [
                                                                (builtin trace)
                                                                (con
                                                                  string
                                                                    "MustHashDatum"
                                                                )
                                                              ]
                                                            ]
                                                            False
                                                          ]
                                                        )
                                                        (force
                                                          [
                                                            [
                                                              {
                                                                [
                                                                  {
                                                                    Maybe_match
                                                                    (con data)
                                                                  }
                                                                  [
                                                                    [
                                                                      findDatum
                                                                      dvh
                                                                    ]
                                                                    ds
                                                                  ]
                                                                ]
                                                                (delayed Bool)
                                                              }
                                                              (lam
                                                                a
                                                                (con data)
                                                                (delay
                                                                  (force
                                                                    [
                                                                      [
                                                                        {
                                                                          [
                                                                            Bool_match
                                                                            [
                                                                              [
                                                                                [
                                                                                  {
                                                                                    (builtin
                                                                                      ifThenElse
                                                                                    )
                                                                                    Bool
                                                                                  }
                                                                                  [
                                                                                    [
                                                                                      (builtin
                                                                                        equalsData
                                                                                      )
                                                                                      a
                                                                                    ]
                                                                                    dv
                                                                                  ]
                                                                                ]
                                                                                True
                                                                              ]
                                                                              False
                                                                            ]
                                                                          ]
                                                                          (delayed Bool)
                                                                        }
                                                                        (delay
                                                                          True
                                                                        )
                                                                      ]
                                                                      (delay j)
                                                                    ]
                                                                  )
                                                                )
                                                              )
                                                            ]
                                                            (delay j)
                                                          ]
                                                        )
                                                      )
                                                    )
                                                  )
                                                ]
                                                (lam
                                                  dv
                                                  (con data)
                                                  [
                                                    { [ TxInfo_match ds ] Bool }
                                                    (lam
                                                      ds
                                                      [List TxInInfo]
                                                      (lam
                                                        ds
                                                        [List TxOut]
                                                        (lam
                                                          ds
                                                          [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                          (lam
                                                            ds
                                                            [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                            (lam
                                                              ds
                                                              [List DCert]
                                                              (lam
                                                                ds
                                                                [List [[Tuple2 StakingCredential] (con integer)]]
                                                                (lam
                                                                  ds
                                                                  [Interval (con integer)]
                                                                  (lam
                                                                    ds
                                                                    [List (con bytestring)]
                                                                    (lam
                                                                      ds
                                                                      [List [[Tuple2 (con bytestring)] (con data)]]
                                                                      (lam
                                                                        ds
                                                                        (con bytestring)
                                                                        (force
                                                                          [
                                                                            [
                                                                              {
                                                                                [
                                                                                  Bool_match
                                                                                  [
                                                                                    [
                                                                                      [
                                                                                        {
                                                                                          {
                                                                                            fFoldableNil_cfoldMap
                                                                                            [(lam a (type) a) Bool]
                                                                                          }
                                                                                          (con data)
                                                                                        }
                                                                                        [
                                                                                          {
                                                                                            fMonoidSum
                                                                                            Bool
                                                                                          }
                                                                                          fAdditiveMonoidBool
                                                                                        ]
                                                                                      ]
                                                                                      [
                                                                                        equalsData
                                                                                        dv
                                                                                      ]
                                                                                    ]
                                                                                    [
                                                                                      [
                                                                                        {
                                                                                          {
                                                                                            fFunctorNil_cfmap
                                                                                            [[Tuple2 (con bytestring)] (con data)]
                                                                                          }
                                                                                          (con data)
                                                                                        }
                                                                                        {
                                                                                          {
                                                                                            snd
                                                                                            (con bytestring)
                                                                                          }
                                                                                          (con data)
                                                                                        }
                                                                                      ]
                                                                                      ds
                                                                                    ]
                                                                                  ]
                                                                                ]
                                                                                (delayed Bool)
                                                                              }
                                                                              (delay
                                                                                True
                                                                              )
                                                                            ]
                                                                            (delay
                                                                              [
                                                                                [
                                                                                  {
                                                                                    (builtin
                                                                                      chooseUnit
                                                                                    )
                                                                                    Bool
                                                                                  }
                                                                                  [
                                                                                    (builtin
                                                                                      trace
                                                                                    )
                                                                                    (con
                                                                                      string
                                                                                        "Missing datum"
                                                                                    )
                                                                                  ]
                                                                                ]
                                                                                False
                                                                              ]
                                                                            )
                                                                          ]
                                                                        )
                                                                      )
                                                                    )
                                                                  )
                                                                )
                                                              )
                                                            )
                                                          )
                                                        )
                                                      )
                                                    )
                                                  ]
                                                )
                                              ]
                                              (lam
                                                mps
                                                (con bytestring)
                                                (lam
                                                  ds
                                                  (con data)
                                                  (lam
                                                    tn
                                                    (con bytestring)
                                                    (lam
                                                      v
                                                      (con integer)
                                                      (force
                                                        [
                                                          [
                                                            {
                                                              [
                                                                Bool_match
                                                                [
                                                                  [
                                                                    [
                                                                      {
                                                                        (builtin
                                                                          ifThenElse
                                                                        )
                                                                        Bool
                                                                      }
                                                                      [
                                                                        [
                                                                          (builtin
                                                                            equalsInteger
                                                                          )
                                                                          [
                                                                            [
                                                                              [
                                                                                valueOf
                                                                                [
                                                                                  {
                                                                                    [
                                                                                      TxInfo_match
                                                                                      ds
                                                                                    ]
                                                                                    [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                  }
                                                                                  (lam
                                                                                    ds
                                                                                    [List TxInInfo]
                                                                                    (lam
                                                                                      ds
                                                                                      [List TxOut]
                                                                                      (lam
                                                                                        ds
                                                                                        [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                        (lam
                                                                                          ds
                                                                                          [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                          (lam
                                                                                            ds
                                                                                            [List DCert]
                                                                                            (lam
                                                                                              ds
                                                                                              [List [[Tuple2 StakingCredential] (con integer)]]
                                                                                              (lam
                                                                                                ds
                                                                                                [Interval (con integer)]
                                                                                                (lam
                                                                                                  ds
                                                                                                  [List (con bytestring)]
                                                                                                  (lam
                                                                                                    ds
                                                                                                    [List [[Tuple2 (con bytestring)] (con data)]]
                                                                                                    (lam
                                                                                                      ds
                                                                                                      (con bytestring)
                                                                                                      ds
                                                                                                    )
                                                                                                  )
                                                                                                )
                                                                                              )
                                                                                            )
                                                                                          )
                                                                                        )
                                                                                      )
                                                                                    )
                                                                                  )
                                                                                ]
                                                                              ]
                                                                              mps
                                                                            ]
                                                                            tn
                                                                          ]
                                                                        ]
                                                                        v
                                                                      ]
                                                                    ]
                                                                    True
                                                                  ]
                                                                  False
                                                                ]
                                                              ]
                                                              (delayed Bool)
                                                            }
                                                            (delay True)
                                                          ]
                                                          (delay
                                                            [
                                                              [
                                                                {
                                                                  (builtin
                                                                    chooseUnit
                                                                  )
                                                                  Bool
                                                                }
                                                                [
                                                                  (builtin trace
                                                                  )
                                                                  (con
                                                                    string
                                                                      "Value minted not OK"
                                                                  )
                                                                ]
                                                              ]
                                                              False
                                                            ]
                                                          )
                                                        ]
                                                      )
                                                    )
                                                  )
                                                )
                                              )
                                            ]
                                            (lam
                                              vlh
                                              (con bytestring)
                                              (lam
                                                dv
                                                (con data)
                                                (lam
                                                  vl
                                                  [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                  (let
                                                    (nonrec)
                                                    (termbind
                                                      (nonstrict)
                                                      (vardecl
                                                        hsh
                                                        [Maybe (con bytestring)]
                                                      )
                                                      [
                                                        [ findDatumHash dv ] ds
                                                      ]
                                                    )
                                                    (termbind
                                                      (nonstrict)
                                                      (vardecl addr Credential)
                                                      [ ScriptCredential vlh ]
                                                    )
                                                    (termbind
                                                      (nonstrict)
                                                      (vardecl addr Address)
                                                      [
                                                        [ Address addr ]
                                                        {
                                                          Nothing
                                                          StakingCredential
                                                        }
                                                      ]
                                                    )
                                                    [
                                                      {
                                                        [ TxInfo_match ds ] Bool
                                                      }
                                                      (lam
                                                        ds
                                                        [List TxInInfo]
                                                        (lam
                                                          ds
                                                          [List TxOut]
                                                          (lam
                                                            ds
                                                            [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                            (lam
                                                              ds
                                                              [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                              (lam
                                                                ds
                                                                [List DCert]
                                                                (lam
                                                                  ds
                                                                  [List [[Tuple2 StakingCredential] (con integer)]]
                                                                  (lam
                                                                    ds
                                                                    [Interval (con integer)]
                                                                    (lam
                                                                      ds
                                                                      [List (con bytestring)]
                                                                      (lam
                                                                        ds
                                                                        [List [[Tuple2 (con bytestring)] (con data)]]
                                                                        (lam
                                                                          ds
                                                                          (con bytestring)
                                                                          (force
                                                                            [
                                                                              [
                                                                                {
                                                                                  [
                                                                                    Bool_match
                                                                                    [
                                                                                      [
                                                                                        [
                                                                                          {
                                                                                            {
                                                                                              fFoldableNil_cfoldMap
                                                                                              [(lam a (type) a) Bool]
                                                                                            }
                                                                                            TxOut
                                                                                          }
                                                                                          [
                                                                                            {
                                                                                              fMonoidSum
                                                                                              Bool
                                                                                            }
                                                                                            fAdditiveMonoidBool
                                                                                          ]
                                                                                        ]
                                                                                        (lam
                                                                                          ds
                                                                                          TxOut
                                                                                          [
                                                                                            {
                                                                                              [
                                                                                                TxOut_match
                                                                                                ds
                                                                                              ]
                                                                                              Bool
                                                                                            }
                                                                                            (lam
                                                                                              ds
                                                                                              Address
                                                                                              (lam
                                                                                                ds
                                                                                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                (lam
                                                                                                  ds
                                                                                                  [Maybe (con bytestring)]
                                                                                                  (force
                                                                                                    [
                                                                                                      [
                                                                                                        {
                                                                                                          [
                                                                                                            {
                                                                                                              Maybe_match
                                                                                                              (con bytestring)
                                                                                                            }
                                                                                                            ds
                                                                                                          ]
                                                                                                          (delayed Bool)
                                                                                                        }
                                                                                                        (lam
                                                                                                          svh
                                                                                                          (con bytestring)
                                                                                                          (delay
                                                                                                            (force
                                                                                                              [
                                                                                                                [
                                                                                                                  {
                                                                                                                    [
                                                                                                                      Bool_match
                                                                                                                      [
                                                                                                                        [
                                                                                                                          [
                                                                                                                            checkBinRel
                                                                                                                            equalsInteger
                                                                                                                          ]
                                                                                                                          ds
                                                                                                                        ]
                                                                                                                        vl
                                                                                                                      ]
                                                                                                                    ]
                                                                                                                    (delayed Bool)
                                                                                                                  }
                                                                                                                  (delay
                                                                                                                    (force
                                                                                                                      [
                                                                                                                        [
                                                                                                                          {
                                                                                                                            [
                                                                                                                              {
                                                                                                                                Maybe_match
                                                                                                                                (con bytestring)
                                                                                                                              }
                                                                                                                              hsh
                                                                                                                            ]
                                                                                                                            (delayed Bool)
                                                                                                                          }
                                                                                                                          (lam
                                                                                                                            a
                                                                                                                            (con bytestring)
                                                                                                                            (delay
                                                                                                                              (force
                                                                                                                                [
                                                                                                                                  [
                                                                                                                                    {
                                                                                                                                      [
                                                                                                                                        Bool_match
                                                                                                                                        [
                                                                                                                                          [
                                                                                                                                            [
                                                                                                                                              {
                                                                                                                                                (builtin
                                                                                                                                                  ifThenElse
                                                                                                                                                )
                                                                                                                                                Bool
                                                                                                                                              }
                                                                                                                                              [
                                                                                                                                                [
                                                                                                                                                  (builtin
                                                                                                                                                    equalsByteString
                                                                                                                                                  )
                                                                                                                                                  a
                                                                                                                                                ]
                                                                                                                                                svh
                                                                                                                                              ]
                                                                                                                                            ]
                                                                                                                                            True
                                                                                                                                          ]
                                                                                                                                          False
                                                                                                                                        ]
                                                                                                                                      ]
                                                                                                                                      (delayed Bool)
                                                                                                                                    }
                                                                                                                                    (delay
                                                                                                                                      [
                                                                                                                                        [
                                                                                                                                          fEqAddress_c
                                                                                                                                          ds
                                                                                                                                        ]
                                                                                                                                        addr
                                                                                                                                      ]
                                                                                                                                    )
                                                                                                                                  ]
                                                                                                                                  (delay
                                                                                                                                    False
                                                                                                                                  )
                                                                                                                                ]
                                                                                                                              )
                                                                                                                            )
                                                                                                                          )
                                                                                                                        ]
                                                                                                                        (delay
                                                                                                                          False
                                                                                                                        )
                                                                                                                      ]
                                                                                                                    )
                                                                                                                  )
                                                                                                                ]
                                                                                                                (delay
                                                                                                                  False
                                                                                                                )
                                                                                                              ]
                                                                                                            )
                                                                                                          )
                                                                                                        )
                                                                                                      ]
                                                                                                      (delay
                                                                                                        False
                                                                                                      )
                                                                                                    ]
                                                                                                  )
                                                                                                )
                                                                                              )
                                                                                            )
                                                                                          ]
                                                                                        )
                                                                                      ]
                                                                                      ds
                                                                                    ]
                                                                                  ]
                                                                                  (delayed Bool)
                                                                                }
                                                                                (delay
                                                                                  True
                                                                                )
                                                                              ]
                                                                              (delay
                                                                                [
                                                                                  [
                                                                                    {
                                                                                      (builtin
                                                                                        chooseUnit
                                                                                      )
                                                                                      Bool
                                                                                    }
                                                                                    [
                                                                                      (builtin
                                                                                        trace
                                                                                      )
                                                                                      (con
                                                                                        string
                                                                                          "MustPayToOtherScript"
                                                                                      )
                                                                                    ]
                                                                                  ]
                                                                                  False
                                                                                ]
                                                                              )
                                                                            ]
                                                                          )
                                                                        )
                                                                      )
                                                                    )
                                                                  )
                                                                )
                                                              )
                                                            )
                                                          )
                                                        )
                                                      )
                                                    ]
                                                  )
                                                )
                                              )
                                            )
                                          ]
                                          (lam
                                            pk
                                            (con bytestring)
                                            (lam
                                              vl
                                              [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                              (force
                                                [
                                                  [
                                                    {
                                                      [
                                                        Bool_match
                                                        [
                                                          [
                                                            [
                                                              checkBinRel
                                                              lessThanEqInteger
                                                            ]
                                                            vl
                                                          ]
                                                          [
                                                            [ valuePaidTo ds ]
                                                            pk
                                                          ]
                                                        ]
                                                      ]
                                                      (delayed Bool)
                                                    }
                                                    (delay True)
                                                  ]
                                                  (delay
                                                    [
                                                      [
                                                        {
                                                          (builtin chooseUnit)
                                                          Bool
                                                        }
                                                        [
                                                          (builtin trace)
                                                          (con
                                                            string
                                                              "MustPayToPubKey"
                                                          )
                                                        ]
                                                      ]
                                                      False
                                                    ]
                                                  )
                                                ]
                                              )
                                            )
                                          )
                                        ]
                                        (lam
                                          vl
                                          [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                          (force
                                            [
                                              [
                                                {
                                                  [
                                                    Bool_match
                                                    [
                                                      [
                                                        [
                                                          checkBinRel
                                                          lessThanEqInteger
                                                        ]
                                                        vl
                                                      ]
                                                      [ valueProduced ds ]
                                                    ]
                                                  ]
                                                  (delayed Bool)
                                                }
                                                (delay True)
                                              ]
                                              (delay
                                                [
                                                  [
                                                    {
                                                      (builtin chooseUnit) Bool
                                                    }
                                                    [
                                                      (builtin trace)
                                                      (con
                                                        string
                                                          "Produced value not OK"
                                                      )
                                                    ]
                                                  ]
                                                  False
                                                ]
                                              )
                                            ]
                                          )
                                        )
                                      ]
                                      (lam
                                        vl
                                        [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                        (force
                                          [
                                            [
                                              {
                                                [
                                                  Bool_match
                                                  [
                                                    [
                                                      [
                                                        checkBinRel
                                                        lessThanEqInteger
                                                      ]
                                                      vl
                                                    ]
                                                    [
                                                      {
                                                        [ TxInfo_match ds ]
                                                        [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                      }
                                                      (lam
                                                        ds
                                                        [List TxInInfo]
                                                        (lam
                                                          ds
                                                          [List TxOut]
                                                          (lam
                                                            ds
                                                            [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                            (lam
                                                              ds
                                                              [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                              (lam
                                                                ds
                                                                [List DCert]
                                                                (lam
                                                                  ds
                                                                  [List [[Tuple2 StakingCredential] (con integer)]]
                                                                  (lam
                                                                    ds
                                                                    [Interval (con integer)]
                                                                    (lam
                                                                      ds
                                                                      [List (con bytestring)]
                                                                      (lam
                                                                        ds
                                                                        [List [[Tuple2 (con bytestring)] (con data)]]
                                                                        (lam
                                                                          ds
                                                                          (con bytestring)
                                                                          [
                                                                            [
                                                                              [
                                                                                {
                                                                                  {
                                                                                    fFoldableNil_cfoldMap
                                                                                    [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                  }
                                                                                  TxInInfo
                                                                                }
                                                                                fMonoidValue
                                                                              ]
                                                                              (lam
                                                                                x
                                                                                TxInInfo
                                                                                [
                                                                                  {
                                                                                    [
                                                                                      TxInInfo_match
                                                                                      x
                                                                                    ]
                                                                                    [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                  }
                                                                                  (lam
                                                                                    ds
                                                                                    TxOutRef
                                                                                    (lam
                                                                                      ds
                                                                                      TxOut
                                                                                      [
                                                                                        {
                                                                                          [
                                                                                            TxOut_match
                                                                                            ds
                                                                                          ]
                                                                                          [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                        }
                                                                                        (lam
                                                                                          ds
                                                                                          Address
                                                                                          (lam
                                                                                            ds
                                                                                            [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                            (lam
                                                                                              ds
                                                                                              [Maybe (con bytestring)]
                                                                                              ds
                                                                                            )
                                                                                          )
                                                                                        )
                                                                                      ]
                                                                                    )
                                                                                  )
                                                                                ]
                                                                              )
                                                                            ]
                                                                            ds
                                                                          ]
                                                                        )
                                                                      )
                                                                    )
                                                                  )
                                                                )
                                                              )
                                                            )
                                                          )
                                                        )
                                                      )
                                                    ]
                                                  ]
                                                ]
                                                (delayed Bool)
                                              }
                                              (delay True)
                                            ]
                                            (delay
                                              [
                                                [
                                                  { (builtin chooseUnit) Bool }
                                                  [
                                                    (builtin trace)
                                                    (con
                                                      string
                                                        "Spent value not OK"
                                                    )
                                                  ]
                                                ]
                                                False
                                              ]
                                            )
                                          ]
                                        )
                                      )
                                    ]
                                    (lam
                                      txOutRef
                                      TxOutRef
                                      (let
                                        (nonrec)
                                        (termbind
                                          (nonstrict)
                                          (vardecl j Bool)
                                          [
                                            [
                                              { (builtin chooseUnit) Bool }
                                              [
                                                (builtin trace)
                                                (con
                                                  string
                                                    "Public key output not spent"
                                                )
                                              ]
                                            ]
                                            False
                                          ]
                                        )
                                        (force
                                          [
                                            [
                                              {
                                                [
                                                  { Maybe_match TxInInfo }
                                                  [
                                                    [
                                                      findTxInByTxOutRef
                                                      txOutRef
                                                    ]
                                                    ds
                                                  ]
                                                ]
                                                (delayed Bool)
                                              }
                                              (lam
                                                a
                                                TxInInfo
                                                (delay
                                                  [
                                                    {
                                                      [ TxInInfo_match a ] Bool
                                                    }
                                                    (lam
                                                      ds
                                                      TxOutRef
                                                      (lam
                                                        ds
                                                        TxOut
                                                        [
                                                          {
                                                            [ TxOut_match ds ]
                                                            Bool
                                                          }
                                                          (lam
                                                            ds
                                                            Address
                                                            (lam
                                                              ds
                                                              [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                              (lam
                                                                ds
                                                                [Maybe (con bytestring)]
                                                                (force
                                                                  [
                                                                    [
                                                                      {
                                                                        [
                                                                          {
                                                                            Maybe_match
                                                                            (con bytestring)
                                                                          }
                                                                          ds
                                                                        ]
                                                                        (delayed Bool)
                                                                      }
                                                                      (lam
                                                                        ds
                                                                        (con bytestring)
                                                                        (delay j
                                                                        )
                                                                      )
                                                                    ]
                                                                    (delay True)
                                                                  ]
                                                                )
                                                              )
                                                            )
                                                          )
                                                        ]
                                                      )
                                                    )
                                                  ]
                                                )
                                              )
                                            ]
                                            (delay j)
                                          ]
                                        )
                                      )
                                    )
                                  ]
                                  (lam
                                    txOutRef
                                    TxOutRef
                                    (lam
                                      ds
                                      (con data)
                                      (force
                                        [
                                          [
                                            {
                                              [
                                                { Maybe_match TxInInfo }
                                                [
                                                  [
                                                    findTxInByTxOutRef txOutRef
                                                  ]
                                                  ds
                                                ]
                                              ]
                                              (delayed Bool)
                                            }
                                            (lam ds TxInInfo (delay True))
                                          ]
                                          (delay
                                            [
                                              [
                                                { (builtin chooseUnit) Bool }
                                                [
                                                  (builtin trace)
                                                  (con
                                                    string
                                                      "Script output not spent"
                                                  )
                                                ]
                                              ]
                                              False
                                            ]
                                          )
                                        ]
                                      )
                                    )
                                  )
                                ]
                                (lam
                                  interval
                                  [Interval (con integer)]
                                  (force
                                    [
                                      [
                                        {
                                          [
                                            Bool_match
                                            [
                                              [
                                                [
                                                  { contains (con integer) }
                                                  fOrdPOSIXTime
                                                ]
                                                interval
                                              ]
                                              [
                                                {
                                                  [ TxInfo_match ds ]
                                                  [Interval (con integer)]
                                                }
                                                (lam
                                                  ds
                                                  [List TxInInfo]
                                                  (lam
                                                    ds
                                                    [List TxOut]
                                                    (lam
                                                      ds
                                                      [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                      (lam
                                                        ds
                                                        [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                        (lam
                                                          ds
                                                          [List DCert]
                                                          (lam
                                                            ds
                                                            [List [[Tuple2 StakingCredential] (con integer)]]
                                                            (lam
                                                              ds
                                                              [Interval (con integer)]
                                                              (lam
                                                                ds
                                                                [List (con bytestring)]
                                                                (lam
                                                                  ds
                                                                  [List [[Tuple2 (con bytestring)] (con data)]]
                                                                  (lam
                                                                    ds
                                                                    (con bytestring)
                                                                    ds
                                                                  )
                                                                )
                                                              )
                                                            )
                                                          )
                                                        )
                                                      )
                                                    )
                                                  )
                                                )
                                              ]
                                            ]
                                          ]
                                          (delayed Bool)
                                        }
                                        (delay True)
                                      ]
                                      (delay
                                        [
                                          [
                                            { (builtin chooseUnit) Bool }
                                            [
                                              (builtin trace)
                                              (con
                                                string
                                                  "Wrong validation interval"
                                              )
                                            ]
                                          ]
                                          False
                                        ]
                                      )
                                    ]
                                  )
                                )
                              ]
                            )
                          )
                        )
                      ]
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      checkScriptContext
                      (all i (type) (all o (type) (fun [(lam a (type) (fun a (con data))) o] (fun [[TxConstraints i] o] (fun ScriptContext Bool)))))
                    )
                    (abs
                      i
                      (type)
                      (abs
                        o
                        (type)
                        (lam
                          dToData
                          [(lam a (type) (fun a (con data))) o]
                          (lam
                            ds
                            [[TxConstraints i] o]
                            (lam
                              ptx
                              ScriptContext
                              [
                                { [ { { TxConstraints_match i } o } ds ] Bool }
                                (lam
                                  ds
                                  [List TxConstraint]
                                  (lam
                                    ds
                                    [List [InputConstraint i]]
                                    (lam
                                      ds
                                      [List [OutputConstraint o]]
                                      (let
                                        (nonrec)
                                        (termbind
                                          (nonstrict)
                                          (vardecl j Bool)
                                          [
                                            [
                                              { (builtin chooseUnit) Bool }
                                              [
                                                (builtin trace)
                                                (con
                                                  string
                                                    "checkScriptContext failed"
                                                )
                                              ]
                                            ]
                                            False
                                          ]
                                        )
                                        (force
                                          [
                                            [
                                              {
                                                [
                                                  Bool_match
                                                  [
                                                    [
                                                      [
                                                        {
                                                          {
                                                            fFoldableNil_cfoldMap
                                                            [(lam a (type) a) Bool]
                                                          }
                                                          TxConstraint
                                                        }
                                                        [
                                                          {
                                                            fMonoidProduct Bool
                                                          }
                                                          fMultiplicativeMonoidBool
                                                        ]
                                                      ]
                                                      [ checkTxConstraint ptx ]
                                                    ]
                                                    ds
                                                  ]
                                                ]
                                                (delayed Bool)
                                              }
                                              (delay
                                                (force
                                                  [
                                                    [
                                                      {
                                                        [
                                                          Bool_match
                                                          [
                                                            [
                                                              [
                                                                {
                                                                  {
                                                                    fFoldableNil_cfoldMap
                                                                    [(lam a (type) a) Bool]
                                                                  }
                                                                  [InputConstraint i]
                                                                }
                                                                [
                                                                  {
                                                                    fMonoidProduct
                                                                    Bool
                                                                  }
                                                                  fMultiplicativeMonoidBool
                                                                ]
                                                              ]
                                                              [
                                                                {
                                                                  checkOwnInputConstraint
                                                                  i
                                                                }
                                                                ptx
                                                              ]
                                                            ]
                                                            ds
                                                          ]
                                                        ]
                                                        (delayed Bool)
                                                      }
                                                      (delay
                                                        (force
                                                          [
                                                            [
                                                              {
                                                                [
                                                                  Bool_match
                                                                  [
                                                                    [
                                                                      [
                                                                        {
                                                                          {
                                                                            fFoldableNil_cfoldMap
                                                                            [(lam a (type) a) Bool]
                                                                          }
                                                                          [OutputConstraint o]
                                                                        }
                                                                        [
                                                                          {
                                                                            fMonoidProduct
                                                                            Bool
                                                                          }
                                                                          fMultiplicativeMonoidBool
                                                                        ]
                                                                      ]
                                                                      [
                                                                        [
                                                                          {
                                                                            checkOwnOutputConstraint
                                                                            o
                                                                          }
                                                                          dToData
                                                                        ]
                                                                        ptx
                                                                      ]
                                                                    ]
                                                                    ds
                                                                  ]
                                                                ]
                                                                (delayed Bool)
                                                              }
                                                              (delay True)
                                                            ]
                                                            (delay j)
                                                          ]
                                                        )
                                                      )
                                                    ]
                                                    (delay j)
                                                  ]
                                                )
                                              )
                                            ]
                                            (delay j)
                                          ]
                                        )
                                      )
                                    )
                                  )
                                )
                              ]
                            )
                          )
                        )
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      isZero
                      (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] Bool)
                    )
                    (lam
                      ds
                      [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                      (let
                        (rec)
                        (termbind
                          (strict)
                          (vardecl
                            go
                            (fun [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]] Bool)
                          )
                          (lam
                            xs
                            [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                            (force
                              [
                                [
                                  {
                                    [
                                      {
                                        Nil_match
                                        [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                      }
                                      xs
                                    ]
                                    (delayed Bool)
                                  }
                                  (delay True)
                                ]
                                (lam
                                  ds
                                  [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                  (lam
                                    xs
                                    [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                    (delay
                                      [
                                        {
                                          [
                                            {
                                              { Tuple2_match (con bytestring) }
                                              [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]
                                            }
                                            ds
                                          ]
                                          Bool
                                        }
                                        (lam
                                          ds
                                          (con bytestring)
                                          (lam
                                            x
                                            [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]
                                            (let
                                              (rec)
                                              (termbind
                                                (strict)
                                                (vardecl
                                                  go
                                                  (fun [List [[Tuple2 (con bytestring)] (con integer)]] Bool)
                                                )
                                                (lam
                                                  xs
                                                  [List [[Tuple2 (con bytestring)] (con integer)]]
                                                  (force
                                                    [
                                                      [
                                                        {
                                                          [
                                                            {
                                                              Nil_match
                                                              [[Tuple2 (con bytestring)] (con integer)]
                                                            }
                                                            xs
                                                          ]
                                                          (delayed Bool)
                                                        }
                                                        (delay [ go xs ])
                                                      ]
                                                      (lam
                                                        ds
                                                        [[Tuple2 (con bytestring)] (con integer)]
                                                        (lam
                                                          xs
                                                          [List [[Tuple2 (con bytestring)] (con integer)]]
                                                          (delay
                                                            [
                                                              {
                                                                [
                                                                  {
                                                                    {
                                                                      Tuple2_match
                                                                      (con bytestring)
                                                                    }
                                                                    (con integer)
                                                                  }
                                                                  ds
                                                                ]
                                                                Bool
                                                              }
                                                              (lam
                                                                ds
                                                                (con bytestring)
                                                                (lam
                                                                  x
                                                                  (con integer)
                                                                  (force
                                                                    [
                                                                      [
                                                                        {
                                                                          [
                                                                            Bool_match
                                                                            [
                                                                              [
                                                                                [
                                                                                  {
                                                                                    (builtin
                                                                                      ifThenElse
                                                                                    )
                                                                                    Bool
                                                                                  }
                                                                                  [
                                                                                    [
                                                                                      (builtin
                                                                                        equalsInteger
                                                                                      )
                                                                                      (con
                                                                                        integer
                                                                                          0
                                                                                      )
                                                                                    ]
                                                                                    x
                                                                                  ]
                                                                                ]
                                                                                True
                                                                              ]
                                                                              False
                                                                            ]
                                                                          ]
                                                                          (delayed Bool)
                                                                        }
                                                                        (delay
                                                                          [
                                                                            go
                                                                            xs
                                                                          ]
                                                                        )
                                                                      ]
                                                                      (delay
                                                                        False
                                                                      )
                                                                    ]
                                                                  )
                                                                )
                                                              )
                                                            ]
                                                          )
                                                        )
                                                      )
                                                    ]
                                                  )
                                                )
                                              )
                                              [ go x ]
                                            )
                                          )
                                        )
                                      ]
                                    )
                                  )
                                )
                              ]
                            )
                          )
                        )
                        [ go ds ]
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      ownHashes
                      (fun ScriptContext [[Tuple2 (con bytestring)] (con bytestring)])
                    )
                    (lam
                      ds
                      ScriptContext
                      (let
                        (nonrec)
                        (termbind
                          (strict)
                          (vardecl
                            fail
                            (fun (all a (type) a) [[Tuple2 (con bytestring)] (con bytestring)])
                          )
                          (lam
                            ds
                            (all a (type) a)
                            [
                              {
                                error
                                [[Tuple2 (con bytestring)] (con bytestring)]
                              }
                              [
                                {
                                  [
                                    Unit_match
                                    [
                                      [
                                        { (builtin chooseUnit) Unit }
                                        [
                                          (builtin trace)
                                          (con
                                            string
                                              "Can't get validator and datum hashes"
                                          )
                                        ]
                                      ]
                                      Unit
                                    ]
                                  ]
                                  (con unit)
                                }
                                (con unit ())
                              ]
                            ]
                          )
                        )
                        (force
                          [
                            [
                              {
                                [ { Maybe_match TxInInfo } [ findOwnInput ds ] ]
                                (delayed [[Tuple2 (con bytestring)] (con bytestring)])
                              }
                              (lam
                                ds
                                TxInInfo
                                (delay
                                  [
                                    {
                                      [ TxInInfo_match ds ]
                                      [[Tuple2 (con bytestring)] (con bytestring)]
                                    }
                                    (lam
                                      ds
                                      TxOutRef
                                      (lam
                                        ds
                                        TxOut
                                        [
                                          {
                                            [ TxOut_match ds ]
                                            [[Tuple2 (con bytestring)] (con bytestring)]
                                          }
                                          (lam
                                            ds
                                            Address
                                            (lam
                                              ds
                                              [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                              (lam
                                                ds
                                                [Maybe (con bytestring)]
                                                [
                                                  {
                                                    [ Address_match ds ]
                                                    [[Tuple2 (con bytestring)] (con bytestring)]
                                                  }
                                                  (lam
                                                    ds
                                                    Credential
                                                    (lam
                                                      ds
                                                      [Maybe StakingCredential]
                                                      [
                                                        [
                                                          {
                                                            [
                                                              Credential_match
                                                              ds
                                                            ]
                                                            [[Tuple2 (con bytestring)] (con bytestring)]
                                                          }
                                                          (lam
                                                            ipv
                                                            (con bytestring)
                                                            [
                                                              fail
                                                              (abs
                                                                e
                                                                (type)
                                                                (error e)
                                                              )
                                                            ]
                                                          )
                                                        ]
                                                        (lam
                                                          s
                                                          (con bytestring)
                                                          (force
                                                            [
                                                              [
                                                                {
                                                                  [
                                                                    {
                                                                      Maybe_match
                                                                      (con bytestring)
                                                                    }
                                                                    ds
                                                                  ]
                                                                  (delayed [[Tuple2 (con bytestring)] (con bytestring)])
                                                                }
                                                                (lam
                                                                  dh
                                                                  (con bytestring)
                                                                  (delay
                                                                    [
                                                                      [
                                                                        {
                                                                          {
                                                                            Tuple2
                                                                            (con bytestring)
                                                                          }
                                                                          (con bytestring)
                                                                        }
                                                                        s
                                                                      ]
                                                                      dh
                                                                    ]
                                                                  )
                                                                )
                                                              ]
                                                              (delay
                                                                [
                                                                  fail
                                                                  (abs
                                                                    e
                                                                    (type)
                                                                    (error e)
                                                                  )
                                                                ]
                                                              )
                                                            ]
                                                          )
                                                        )
                                                      ]
                                                    )
                                                  )
                                                ]
                                              )
                                            )
                                          )
                                        ]
                                      )
                                    )
                                  ]
                                )
                              )
                            ]
                            (delay [ fail (abs e (type) (error e)) ])
                          ]
                        )
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl ownHash (fun ScriptContext (con bytestring)))
                    (lam
                      p
                      ScriptContext
                      [
                        {
                          [
                            {
                              { Tuple2_match (con bytestring) } (con bytestring)
                            }
                            [ ownHashes p ]
                          ]
                          (con bytestring)
                        }
                        (lam a (con bytestring) (lam ds (con bytestring) a))
                      ]
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      b
                      (fun (con bytestring) [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]])
                    )
                    (lam
                      ds
                      (con bytestring)
                      {
                        Nil
                        [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                      }
                    )
                  )
                  (termbind
                    (nonstrict)
                    (vardecl
                      threadTokenValueInner
                      (fun [Maybe ThreadToken] (fun (con bytestring) [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]))
                    )
                    (lam
                      m
                      [Maybe ThreadToken]
                      (force
                        [
                          [
                            {
                              [ { Maybe_match ThreadToken } m ]
                              (delayed (fun (con bytestring) [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]))
                            }
                            (lam
                              a
                              ThreadToken
                              (let
                                (nonrec)
                                (termbind
                                  (nonstrict)
                                  (vardecl currency (con bytestring))
                                  [
                                    { [ ThreadToken_match a ] (con bytestring) }
                                    (lam
                                      ds TxOutRef (lam ds (con bytestring) ds)
                                    )
                                  ]
                                )
                                (delay
                                  (lam
                                    ds
                                    (con bytestring)
                                    [
                                      [
                                        {
                                          Cons
                                          [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                        }
                                        [
                                          [
                                            {
                                              { Tuple2 (con bytestring) }
                                              [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]
                                            }
                                            currency
                                          ]
                                          [
                                            [
                                              {
                                                Cons
                                                [[Tuple2 (con bytestring)] (con integer)]
                                              }
                                              [
                                                [
                                                  {
                                                    { Tuple2 (con bytestring) }
                                                    (con integer)
                                                  }
                                                  ds
                                                ]
                                                (con integer 1)
                                              ]
                                            ]
                                            {
                                              Nil
                                              [[Tuple2 (con bytestring)] (con integer)]
                                            }
                                          ]
                                        ]
                                      ]
                                      {
                                        Nil
                                        [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                      }
                                    ]
                                  )
                                )
                              )
                            )
                          ]
                          (delay b)
                        ]
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      wmkValidator
                      (all s (type) (all i (type) (fun [(lam a (type) (fun a (con data))) s] (fun (fun [State s] (fun i [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State s]]])) (fun (fun s Bool) (fun (fun s (fun i (fun ScriptContext Bool))) (fun [Maybe ThreadToken] (fun s (fun i (fun ScriptContext Bool))))))))))
                    )
                    (abs
                      s
                      (type)
                      (abs
                        i
                        (type)
                        (lam
                          w
                          [(lam a (type) (fun a (con data))) s]
                          (lam
                            ww
                            (fun [State s] (fun i [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State s]]]))
                            (lam
                              ww
                              (fun s Bool)
                              (lam
                                ww
                                (fun s (fun i (fun ScriptContext Bool)))
                                (lam
                                  ww
                                  [Maybe ThreadToken]
                                  (lam
                                    w
                                    s
                                    (lam
                                      w
                                      i
                                      (lam
                                        w
                                        ScriptContext
                                        (let
                                          (nonrec)
                                          (termbind
                                            (nonstrict)
                                            (vardecl
                                              vl
                                              [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                            )
                                            (force
                                              [
                                                [
                                                  {
                                                    [
                                                      { Maybe_match TxInInfo }
                                                      [ findOwnInput w ]
                                                    ]
                                                    (delayed [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]])
                                                  }
                                                  (lam
                                                    a
                                                    TxInInfo
                                                    (delay
                                                      [
                                                        {
                                                          [ TxInInfo_match a ]
                                                          [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                        }
                                                        (lam
                                                          ds
                                                          TxOutRef
                                                          (lam
                                                            ds
                                                            TxOut
                                                            [
                                                              {
                                                                [
                                                                  TxOut_match ds
                                                                ]
                                                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                              }
                                                              (lam
                                                                ds
                                                                Address
                                                                (lam
                                                                  ds
                                                                  [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                  (lam
                                                                    ds
                                                                    [Maybe (con bytestring)]
                                                                    ds
                                                                  )
                                                                )
                                                              )
                                                            ]
                                                          )
                                                        )
                                                      ]
                                                    )
                                                  )
                                                ]
                                                (delay
                                                  [
                                                    {
                                                      error
                                                      [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                    }
                                                    [
                                                      {
                                                        [
                                                          Unit_match
                                                          [
                                                            [
                                                              {
                                                                (builtin
                                                                  chooseUnit
                                                                )
                                                                Unit
                                                              }
                                                              [
                                                                (builtin trace)
                                                                (con
                                                                  string
                                                                    "Can't find validation input"
                                                                )
                                                              ]
                                                            ]
                                                            Unit
                                                          ]
                                                        ]
                                                        (con unit)
                                                      }
                                                      (con unit ())
                                                    ]
                                                  ]
                                                )
                                              ]
                                            )
                                          )
                                          (termbind
                                            (nonstrict)
                                            (vardecl j Bool)
                                            (force
                                              [
                                                [
                                                  {
                                                    [
                                                      {
                                                        Maybe_match
                                                        [[Tuple2 [[TxConstraints Void] Void]] [State s]]
                                                      }
                                                      [
                                                        [
                                                          ww
                                                          [
                                                            [ { State s } w ]
                                                            [
                                                              [
                                                                [
                                                                  unionWith
                                                                  addInteger
                                                                ]
                                                                vl
                                                              ]
                                                              [
                                                                [
                                                                  fAdditiveGroupValue_cscale
                                                                  (con
                                                                    integer -1
                                                                  )
                                                                ]
                                                                [
                                                                  [
                                                                    threadTokenValueInner
                                                                    ww
                                                                  ]
                                                                  [ ownHash w ]
                                                                ]
                                                              ]
                                                            ]
                                                          ]
                                                        ]
                                                        w
                                                      ]
                                                    ]
                                                    (delayed Bool)
                                                  }
                                                  (lam
                                                    ds
                                                    [[Tuple2 [[TxConstraints Void] Void]] [State s]]
                                                    (delay
                                                      [
                                                        {
                                                          [
                                                            {
                                                              {
                                                                Tuple2_match
                                                                [[TxConstraints Void] Void]
                                                              }
                                                              [State s]
                                                            }
                                                            ds
                                                          ]
                                                          Bool
                                                        }
                                                        (lam
                                                          newConstraints
                                                          [[TxConstraints Void] Void]
                                                          (lam
                                                            ds
                                                            [State s]
                                                            [
                                                              {
                                                                [
                                                                  {
                                                                    State_match
                                                                    s
                                                                  }
                                                                  ds
                                                                ]
                                                                Bool
                                                              }
                                                              (lam
                                                                ds
                                                                s
                                                                (lam
                                                                  ds
                                                                  [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                  (let
                                                                    (nonrec)
                                                                    (termbind
                                                                      (nonstrict
                                                                      )
                                                                      (vardecl
                                                                        j Bool
                                                                      )
                                                                      (force
                                                                        [
                                                                          [
                                                                            {
                                                                              [
                                                                                Bool_match
                                                                                [
                                                                                  [
                                                                                    [
                                                                                      {
                                                                                        {
                                                                                          checkScriptContext
                                                                                          Void
                                                                                        }
                                                                                        Void
                                                                                      }
                                                                                      {
                                                                                        absurd
                                                                                        (con data)
                                                                                      }
                                                                                    ]
                                                                                    newConstraints
                                                                                  ]
                                                                                  w
                                                                                ]
                                                                              ]
                                                                              (delayed Bool)
                                                                            }
                                                                            (delay
                                                                              True
                                                                            )
                                                                          ]
                                                                          (delay
                                                                            [
                                                                              [
                                                                                {
                                                                                  (builtin
                                                                                    chooseUnit
                                                                                  )
                                                                                  Bool
                                                                                }
                                                                                [
                                                                                  (builtin
                                                                                    trace
                                                                                  )
                                                                                  (con
                                                                                    string
                                                                                      "State transition invalid - constraints not satisfied by ScriptContext"
                                                                                  )
                                                                                ]
                                                                              ]
                                                                              False
                                                                            ]
                                                                          )
                                                                        ]
                                                                      )
                                                                    )
                                                                    (force
                                                                      [
                                                                        [
                                                                          {
                                                                            [
                                                                              Bool_match
                                                                              [
                                                                                ww
                                                                                ds
                                                                              ]
                                                                            ]
                                                                            (delayed Bool)
                                                                          }
                                                                          (delay
                                                                            (force
                                                                              [
                                                                                [
                                                                                  {
                                                                                    [
                                                                                      Bool_match
                                                                                      [
                                                                                        isZero
                                                                                        ds
                                                                                      ]
                                                                                    ]
                                                                                    (delayed Bool)
                                                                                  }
                                                                                  (delay
                                                                                    j
                                                                                  )
                                                                                ]
                                                                                (delay
                                                                                  (force
                                                                                    [
                                                                                      [
                                                                                        {
                                                                                          [
                                                                                            Bool_match
                                                                                            [
                                                                                              [
                                                                                                {
                                                                                                  (builtin
                                                                                                    chooseUnit
                                                                                                  )
                                                                                                  Bool
                                                                                                }
                                                                                                [
                                                                                                  (builtin
                                                                                                    trace
                                                                                                  )
                                                                                                  (con
                                                                                                    string
                                                                                                      "Non-zero value allocated in final state"
                                                                                                  )
                                                                                                ]
                                                                                              ]
                                                                                              False
                                                                                            ]
                                                                                          ]
                                                                                          (delayed Bool)
                                                                                        }
                                                                                        (delay
                                                                                          j
                                                                                        )
                                                                                      ]
                                                                                      (delay
                                                                                        False
                                                                                      )
                                                                                    ]
                                                                                  )
                                                                                )
                                                                              ]
                                                                            )
                                                                          )
                                                                        ]
                                                                        (delay
                                                                          (force
                                                                            [
                                                                              [
                                                                                {
                                                                                  [
                                                                                    Bool_match
                                                                                    [
                                                                                      [
                                                                                        [
                                                                                          {
                                                                                            {
                                                                                              checkScriptContext
                                                                                              Void
                                                                                            }
                                                                                            s
                                                                                          }
                                                                                          w
                                                                                        ]
                                                                                        [
                                                                                          {
                                                                                            [
                                                                                              {
                                                                                                {
                                                                                                  TxConstraints_match
                                                                                                  Void
                                                                                                }
                                                                                                Void
                                                                                              }
                                                                                              newConstraints
                                                                                            ]
                                                                                            [[TxConstraints Void] s]
                                                                                          }
                                                                                          (lam
                                                                                            ds
                                                                                            [List TxConstraint]
                                                                                            (lam
                                                                                              ds
                                                                                              [List [InputConstraint Void]]
                                                                                              (lam
                                                                                                ds
                                                                                                [List [OutputConstraint Void]]
                                                                                                [
                                                                                                  [
                                                                                                    [
                                                                                                      {
                                                                                                        {
                                                                                                          TxConstraints
                                                                                                          Void
                                                                                                        }
                                                                                                        s
                                                                                                      }
                                                                                                      ds
                                                                                                    ]
                                                                                                    ds
                                                                                                  ]
                                                                                                  [
                                                                                                    {
                                                                                                      build
                                                                                                      [OutputConstraint s]
                                                                                                    }
                                                                                                    (abs
                                                                                                      a
                                                                                                      (type)
                                                                                                      (lam
                                                                                                        c
                                                                                                        (fun [OutputConstraint s] (fun a a))
                                                                                                        (lam
                                                                                                          n
                                                                                                          a
                                                                                                          [
                                                                                                            [
                                                                                                              c
                                                                                                              [
                                                                                                                [
                                                                                                                  {
                                                                                                                    OutputConstraint
                                                                                                                    s
                                                                                                                  }
                                                                                                                  ds
                                                                                                                ]
                                                                                                                [
                                                                                                                  [
                                                                                                                    [
                                                                                                                      unionWith
                                                                                                                      addInteger
                                                                                                                    ]
                                                                                                                    ds
                                                                                                                  ]
                                                                                                                  [
                                                                                                                    [
                                                                                                                      threadTokenValueInner
                                                                                                                      ww
                                                                                                                    ]
                                                                                                                    [
                                                                                                                      ownHash
                                                                                                                      w
                                                                                                                    ]
                                                                                                                  ]
                                                                                                                ]
                                                                                                              ]
                                                                                                            ]
                                                                                                            n
                                                                                                          ]
                                                                                                        )
                                                                                                      )
                                                                                                    )
                                                                                                  ]
                                                                                                ]
                                                                                              )
                                                                                            )
                                                                                          )
                                                                                        ]
                                                                                      ]
                                                                                      w
                                                                                    ]
                                                                                  ]
                                                                                  (delayed Bool)
                                                                                }
                                                                                (delay
                                                                                  True
                                                                                )
                                                                              ]
                                                                              (delay
                                                                                [
                                                                                  [
                                                                                    {
                                                                                      (builtin
                                                                                        chooseUnit
                                                                                      )
                                                                                      Bool
                                                                                    }
                                                                                    [
                                                                                      (builtin
                                                                                        trace
                                                                                      )
                                                                                      (con
                                                                                        string
                                                                                          "State transition invalid - constraints not satisfied by ScriptContext"
                                                                                      )
                                                                                    ]
                                                                                  ]
                                                                                  False
                                                                                ]
                                                                              )
                                                                            ]
                                                                          )
                                                                        )
                                                                      ]
                                                                    )
                                                                  )
                                                                )
                                                              )
                                                            ]
                                                          )
                                                        )
                                                      ]
                                                    )
                                                  )
                                                ]
                                                (delay
                                                  [
                                                    [
                                                      {
                                                        (builtin chooseUnit)
                                                        Bool
                                                      }
                                                      [
                                                        (builtin trace)
                                                        (con
                                                          string
                                                            "State transition invalid - input is not a valid transition at the current state"
                                                        )
                                                      ]
                                                    ]
                                                    False
                                                  ]
                                                )
                                              ]
                                            )
                                          )
                                          (termbind
                                            (nonstrict)
                                            (vardecl j Bool)
                                            (force
                                              [
                                                [
                                                  {
                                                    [
                                                      {
                                                        Maybe_match ThreadToken
                                                      }
                                                      ww
                                                    ]
                                                    (delayed Bool)
                                                  }
                                                  (lam
                                                    threadToken
                                                    ThreadToken
                                                    (delay
                                                      (force
                                                        [
                                                          [
                                                            {
                                                              [
                                                                Bool_match
                                                                [
                                                                  [
                                                                    [
                                                                      {
                                                                        (builtin
                                                                          ifThenElse
                                                                        )
                                                                        Bool
                                                                      }
                                                                      [
                                                                        [
                                                                          (builtin
                                                                            equalsInteger
                                                                          )
                                                                          [
                                                                            [
                                                                              [
                                                                                valueOf
                                                                                vl
                                                                              ]
                                                                              [
                                                                                {
                                                                                  [
                                                                                    ThreadToken_match
                                                                                    threadToken
                                                                                  ]
                                                                                  (con bytestring)
                                                                                }
                                                                                (lam
                                                                                  ds
                                                                                  TxOutRef
                                                                                  (lam
                                                                                    ds
                                                                                    (con bytestring)
                                                                                    ds
                                                                                  )
                                                                                )
                                                                              ]
                                                                            ]
                                                                            [
                                                                              ownHash
                                                                              w
                                                                            ]
                                                                          ]
                                                                        ]
                                                                        (con
                                                                          integer
                                                                            1
                                                                        )
                                                                      ]
                                                                    ]
                                                                    True
                                                                  ]
                                                                  False
                                                                ]
                                                              ]
                                                              (delayed Bool)
                                                            }
                                                            (delay j)
                                                          ]
                                                          (delay
                                                            (force
                                                              [
                                                                [
                                                                  {
                                                                    [
                                                                      Bool_match
                                                                      [
                                                                        [
                                                                          {
                                                                            (builtin
                                                                              chooseUnit
                                                                            )
                                                                            Bool
                                                                          }
                                                                          [
                                                                            (builtin
                                                                              trace
                                                                            )
                                                                            (con
                                                                              string
                                                                                "Thread token not found"
                                                                            )
                                                                          ]
                                                                        ]
                                                                        False
                                                                      ]
                                                                    ]
                                                                    (delayed Bool)
                                                                  }
                                                                  (delay j)
                                                                ]
                                                                (delay False)
                                                              ]
                                                            )
                                                          )
                                                        ]
                                                      )
                                                    )
                                                  )
                                                ]
                                                (delay j)
                                              ]
                                            )
                                          )
                                          (force
                                            [
                                              [
                                                {
                                                  [
                                                    Bool_match
                                                    [ [ [ ww w ] w ] w ]
                                                  ]
                                                  (delayed Bool)
                                                }
                                                (delay j)
                                              ]
                                              (delay
                                                (force
                                                  [
                                                    [
                                                      {
                                                        [
                                                          Bool_match
                                                          [
                                                            [
                                                              {
                                                                (builtin
                                                                  chooseUnit
                                                                )
                                                                Bool
                                                              }
                                                              [
                                                                (builtin trace)
                                                                (con
                                                                  string
                                                                    "State transition invalid - checks failed"
                                                                )
                                                              ]
                                                            ]
                                                            False
                                                          ]
                                                        ]
                                                        (delayed Bool)
                                                      }
                                                      (delay j)
                                                    ]
                                                    (delay False)
                                                  ]
                                                )
                                              )
                                            ]
                                          )
                                        )
                                      )
                                    )
                                  )
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      mkValidator
                      (all s (type) (all i (type) (fun [(lam a (type) (fun a (con data))) s] (fun [[StateMachine s] i] (fun s (fun i (fun ScriptContext Bool)))))))
                    )
                    (abs
                      s
                      (type)
                      (abs
                        i
                        (type)
                        (lam
                          w
                          [(lam a (type) (fun a (con data))) s]
                          (lam
                            w
                            [[StateMachine s] i]
                            (lam
                              w
                              s
                              (lam
                                w
                                i
                                (lam
                                  w
                                  ScriptContext
                                  [
                                    {
                                      [ { { StateMachine_match s } i } w ] Bool
                                    }
                                    (lam
                                      ww
                                      (fun [State s] (fun i [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State s]]]))
                                      (lam
                                        ww
                                        (fun s Bool)
                                        (lam
                                          ww
                                          (fun s (fun i (fun ScriptContext Bool)))
                                          (lam
                                            ww
                                            [Maybe ThreadToken]
                                            [
                                              [
                                                [
                                                  [
                                                    [
                                                      [
                                                        [
                                                          [
                                                            {
                                                              { wmkValidator s }
                                                              i
                                                            }
                                                            w
                                                          ]
                                                          ww
                                                        ]
                                                        ww
                                                      ]
                                                      ww
                                                    ]
                                                    ww
                                                  ]
                                                  w
                                                ]
                                                w
                                              ]
                                              w
                                            ]
                                          )
                                        )
                                      )
                                    )
                                  ]
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                  (termbind
                    (strict)
                    (vardecl
                      mkValidator
                      (fun Params (fun MSState (fun Input (fun ScriptContext Bool))))
                    )
                    (lam
                      params
                      Params
                      [
                        [
                          { { mkValidator MSState } Input }
                          fToDataMSState_ctoBuiltinData
                        ]
                        [ machine params ]
                      ]
                    )
                  )
                  mkValidator
                )
              )
            )
          )
        )
      )
    )
  )
)