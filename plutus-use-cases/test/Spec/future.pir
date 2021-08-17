(program
  (let
    (nonrec)
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
        (termbind
          (strict)
          (vardecl
            fFromDataMap
            (all v (type) (all k (type) [Maybe [List [[Tuple2 k] v]]]))
          )
          (abs
            v
            (type)
            (abs
              k (type) [ { Just [List [[Tuple2 k] v]] } { Nil [[Tuple2 k] v] } ]
            )
          )
        )
        (datatypebind
          (datatype (tyvardecl Unit (type))  Unit_match (vardecl Unit Unit))
        )
        (termbind
          (strict)
          (vardecl
            fFromDataMap
            (all v (type) (all k (type) (fun Unit [Maybe [List [[Tuple2 k] v]]])))
          )
          (abs v (type) (abs k (type) (lam ds Unit { { fFromDataMap v } k })))
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
            (tyvardecl ThreadToken (type))

            ThreadToken_match
            (vardecl
              ThreadToken (fun TxOutRef (fun (con bytestring) ThreadToken))
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
            (tyvardecl Bool (type))

            Bool_match
            (vardecl True Bool) (vardecl False Bool)
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
        (let
          (rec)
          (datatypebind
            (datatype
              (tyvardecl TxConstraint (type))

              TxConstraint_match
              (vardecl MustBeSignedBy (fun (con bytestring) TxConstraint))
              (vardecl
                MustHashDatum
                (fun (con bytestring) (fun (con data) TxConstraint))
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
              (vardecl MustSatisfyAnyOf (fun [List TxConstraint] TxConstraint))
              (vardecl
                MustSpendAtLeast
                (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] TxConstraint)
              )
              (vardecl MustSpendPubKeyOutput (fun TxOutRef TxConstraint))
              (vardecl
                MustSpendScriptOutput
                (fun TxOutRef (fun (con data) TxConstraint))
              )
              (vardecl
                MustValidateIn (fun [Interval (con integer)] TxConstraint)
              )
            )
          )
          (let
            (nonrec)
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
                mkStateMachine
                (all s (type) (all i (type) (fun s (fun i (fun ScriptContext Bool)))))
              )
              (abs
                s
                (type)
                (abs i (type) (lam ds s (lam ds i (lam ds ScriptContext True))))
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
                        {
                          [
                            [
                              {
                                [ { Nil_match a } l ] (all dead (type) [List b])
                              }
                              (abs dead (type) { Nil b })
                            ]
                            (lam
                              x
                              a
                              (lam
                                xs
                                [List a]
                                (abs
                                  dead
                                  (type)
                                  [
                                    [ { Cons b } [ f x ] ]
                                    [ [ { { fFunctorNil_cfmap a } b } f ] xs ]
                                  ]
                                )
                              )
                            )
                          ]
                          (all dead (type) dead)
                        }
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
                    fAdditiveGroupValue_cscale
                    (fun (con integer) (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]))
                  )
                  (lam
                    i
                    (con integer)
                    (lam
                      ds
                      [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                      [
                        [
                          {
                            {
                              fFunctorNil_cfmap
                              [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                            }
                            [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                          }
                          (lam
                            ds
                            [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                            [
                              {
                                [
                                  {
                                    { Tuple2_match (con bytestring) }
                                    [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]
                                  }
                                  ds
                                ]
                                [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                              }
                              (lam
                                c
                                (con bytestring)
                                (lam
                                  a
                                  [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]
                                  [
                                    [
                                      {
                                        { Tuple2 (con bytestring) }
                                        [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]
                                      }
                                      c
                                    ]
                                    [
                                      [
                                        {
                                          {
                                            fFunctorNil_cfmap
                                            [[Tuple2 (con bytestring)] (con integer)]
                                          }
                                          [[Tuple2 (con bytestring)] (con integer)]
                                        }
                                        (lam
                                          ds
                                          [[Tuple2 (con bytestring)] (con integer)]
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
                                              [[Tuple2 (con bytestring)] (con integer)]
                                            }
                                            (lam
                                              c
                                              (con bytestring)
                                              (lam
                                                a
                                                (con integer)
                                                [
                                                  [
                                                    {
                                                      {
                                                        Tuple2 (con bytestring)
                                                      }
                                                      (con integer)
                                                    }
                                                    c
                                                  ]
                                                  [
                                                    [
                                                      (builtin multiplyInteger)
                                                      i
                                                    ]
                                                    a
                                                  ]
                                                ]
                                              )
                                            )
                                          ]
                                        )
                                      ]
                                      a
                                    ]
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
                (termbind
                  (strict)
                  (vardecl
                    addInteger
                    (fun (con integer) (fun (con integer) (con integer)))
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
                    equalsByteString
                    (fun (con bytestring) (fun (con bytestring) Bool))
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
                    (tyvardecl These (fun (type) (fun (type) (type))))
                    (tyvardecl a (type)) (tyvardecl b (type))
                    These_match
                    (vardecl That (fun b [[These a] b]))
                    (vardecl These (fun a (fun b [[These a] b])))
                    (vardecl This (fun a [[These a] b]))
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
                      {
                        [
                          [
                            { [ Bool_match ds ] (all dead (type) Bool) }
                            (abs dead (type) True)
                          ]
                          (abs dead (type) ds)
                        ]
                        (all dead (type) dead)
                      }
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
                          [ { Monoid_match a } v ]
                          [(lam a (type) (fun a (fun a a))) a]
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
                              (vardecl
                                dSemigroup [(lam a (type) (fun a (fun a a))) m]
                              )
                              [ { p1Monoid m } dMonoid ]
                            )
                            (lam
                              ds
                              (fun a m)
                              (lam
                                ds
                                [List a]
                                {
                                  [
                                    [
                                      {
                                        [ { Nil_match a } ds ]
                                        (all dead (type) m)
                                      }
                                      (abs dead (type) [ { mempty m } dMonoid ])
                                    ]
                                    (lam
                                      x
                                      a
                                      (lam
                                        xs
                                        [List a]
                                        (abs
                                          dead
                                          (type)
                                          [
                                            [ dSemigroup [ ds x ] ]
                                            [
                                              [
                                                [
                                                  {
                                                    { fFoldableNil_cfoldMap m }
                                                    a
                                                  }
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
                                  (all dead (type) dead)
                                }
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
                            (lam
                              v [(lam a (type) (fun a (fun a a))) a] (lam v a v)
                            )
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
                                  {
                                    [
                                      [
                                        {
                                          [ { Nil_match a } l ]
                                          (all dead (type) b)
                                        }
                                        (abs dead (type) acc)
                                      ]
                                      (lam
                                        x
                                        a
                                        (lam
                                          xs
                                          [List a]
                                          (abs
                                            dead
                                            (type)
                                            [
                                              [ f x ]
                                              [
                                                [ [ { { foldr a } b } f ] acc ]
                                                xs
                                              ]
                                            ]
                                          )
                                        )
                                      )
                                    ]
                                    (all dead (type) dead)
                                  }
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
                                              {
                                                foldr [[Tuple2 k] [[These v] r]]
                                              }
                                              [List [[Tuple2 k] [[These v] r]]]
                                            }
                                            { Cons [[Tuple2 k] [[These v] r]] }
                                          ]
                                          [
                                            [
                                              {
                                                {
                                                  fFunctorNil_cfmap
                                                  [[Tuple2 k] r]
                                                }
                                                [[Tuple2 k] [[These v] r]]
                                              }
                                              (lam
                                                ds
                                                [[Tuple2 k] r]
                                                [
                                                  {
                                                    [
                                                      { { Tuple2_match k } r }
                                                      ds
                                                    ]
                                                    [[Tuple2 k] [[These v] r]]
                                                  }
                                                  (lam
                                                    c
                                                    k
                                                    (lam
                                                      a
                                                      r
                                                      [
                                                        [
                                                          {
                                                            { Tuple2 k }
                                                            [[These v] r]
                                                          }
                                                          c
                                                        ]
                                                        [ { { That v } r } a ]
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
                                                            {
                                                              { Tuple2_match k }
                                                              r
                                                            }
                                                            e
                                                          ]
                                                          [List [[Tuple2 k] r]]
                                                        }
                                                        (lam
                                                          c
                                                          k
                                                          (lam
                                                            ds
                                                            r
                                                            {
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
                                                                    (all dead (type) [List [[Tuple2 k] r]])
                                                                  }
                                                                  (abs
                                                                    dead
                                                                    (type)
                                                                    xs
                                                                  )
                                                                ]
                                                                (abs
                                                                  dead
                                                                  (type)
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
                                                              (all dead (type) dead)
                                                            }
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
                                              {
                                                fFunctorNil_cfmap [[Tuple2 k] v]
                                              }
                                              [[Tuple2 k] [[These v] r]]
                                            }
                                            (lam
                                              ds
                                              [[Tuple2 k] v]
                                              [
                                                {
                                                  [
                                                    { { Tuple2_match k } v } ds
                                                  ]
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
                                                          {
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
                                                                  (all dead (type) [[These v] r])
                                                                }
                                                                (abs
                                                                  dead
                                                                  (type)
                                                                  [
                                                                    {
                                                                      { This v }
                                                                      r
                                                                    }
                                                                    i
                                                                  ]
                                                                )
                                                              ]
                                                              (lam
                                                                ds
                                                                [[Tuple2 k] r]
                                                                (lam
                                                                  xs
                                                                  [List [[Tuple2 k] r]]
                                                                  (abs
                                                                    dead
                                                                    (type)
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
                                                                          {
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
                                                                                  (all dead (type) [[These v] r])
                                                                                }
                                                                                (abs
                                                                                  dead
                                                                                  (type)
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
                                                                              (abs
                                                                                dead
                                                                                (type)
                                                                                [
                                                                                  go
                                                                                  xs
                                                                                ]
                                                                              )
                                                                            ]
                                                                            (all dead (type) dead)
                                                                          }
                                                                        )
                                                                      )
                                                                    ]
                                                                  )
                                                                )
                                                              )
                                                            ]
                                                            (all dead (type) dead)
                                                          }
                                                        )
                                                      )
                                                      [
                                                        [
                                                          {
                                                            { Tuple2 k }
                                                            [[These v] r]
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
                              [
                                [
                                  {
                                    {
                                      fFunctorNil_cfmap
                                      [[Tuple2 (con bytestring)] [[These [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                    }
                                    [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]]
                                  }
                                  (lam
                                    ds
                                    [[Tuple2 (con bytestring)] [[These [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                    [
                                      {
                                        [
                                          {
                                            { Tuple2_match (con bytestring) }
                                            [[These [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                          }
                                          ds
                                        ]
                                        [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]]
                                      }
                                      (lam
                                        c
                                        (con bytestring)
                                        (lam
                                          a
                                          [[These [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                          [
                                            [
                                              {
                                                { Tuple2 (con bytestring) }
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
                                                      a
                                                    ]
                                                    [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]
                                                  }
                                                  (lam
                                                    b
                                                    [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]
                                                    [
                                                      [
                                                        {
                                                          {
                                                            fFunctorNil_cfmap
                                                            [[Tuple2 (con bytestring)] (con integer)]
                                                          }
                                                          [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]
                                                        }
                                                        (lam
                                                          ds
                                                          [[Tuple2 (con bytestring)] (con integer)]
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
                                                              [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]
                                                            }
                                                            (lam
                                                              c
                                                              (con bytestring)
                                                              (lam
                                                                a
                                                                (con integer)
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
                                                                    a
                                                                  ]
                                                                ]
                                                              )
                                                            )
                                                          ]
                                                        )
                                                      ]
                                                      b
                                                    ]
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
                                                [
                                                  [
                                                    {
                                                      {
                                                        fFunctorNil_cfmap
                                                        [[Tuple2 (con bytestring)] (con integer)]
                                                      }
                                                      [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]
                                                    }
                                                    (lam
                                                      ds
                                                      [[Tuple2 (con bytestring)] (con integer)]
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
                                                          [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]
                                                        }
                                                        (lam
                                                          c
                                                          (con bytestring)
                                                          (lam
                                                            a
                                                            (con integer)
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
                                                                a
                                                              ]
                                                            ]
                                                          )
                                                        )
                                                      ]
                                                    )
                                                  ]
                                                  a
                                                ]
                                              )
                                            ]
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
                                [
                                  [
                                    {
                                      {
                                        fFunctorNil_cfmap
                                        [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]]
                                      }
                                      [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                    }
                                    (lam
                                      ds
                                      [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]]
                                      [
                                        {
                                          [
                                            {
                                              { Tuple2_match (con bytestring) }
                                              [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]
                                            }
                                            ds
                                          ]
                                          [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                        }
                                        (lam
                                          c
                                          (con bytestring)
                                          (lam
                                            a
                                            [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]
                                            [
                                              [
                                                {
                                                  { Tuple2 (con bytestring) }
                                                  [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]
                                                }
                                                c
                                              ]
                                              [
                                                [
                                                  {
                                                    {
                                                      fFunctorNil_cfmap
                                                      [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]
                                                    }
                                                    [[Tuple2 (con bytestring)] (con integer)]
                                                  }
                                                  (lam
                                                    ds
                                                    [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]
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
                                                        [[Tuple2 (con bytestring)] (con integer)]
                                                      }
                                                      (lam
                                                        c
                                                        (con bytestring)
                                                        (lam
                                                          a
                                                          [[These (con integer)] (con integer)]
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
                                                                      a
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
                                                                      [ f a ] b
                                                                    ]
                                                                  )
                                                                )
                                                              ]
                                                              (lam
                                                                a
                                                                (con integer)
                                                                [
                                                                  [ f a ]
                                                                  (con integer 0
                                                                  )
                                                                ]
                                                              )
                                                            ]
                                                          ]
                                                        )
                                                      )
                                                    ]
                                                  )
                                                ]
                                                a
                                              ]
                                            ]
                                          )
                                        )
                                      ]
                                    )
                                  ]
                                  [ [ unionVal ls ] rs ]
                                ]
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
                                [
                                  [
                                    fAdditiveGroupValue_cscale (con integer -1)
                                  ]
                                  ds
                                ]
                              ]
                            )
                          )
                        )
                        (termbind
                          (strict)
                          (vardecl
                            fMonoidTxConstraints_c
                            (all i (type) (all o (type) (fun [[TxConstraints i] o] (fun [[TxConstraints i] o] [[TxConstraints i] o]))))
                          )
                          (abs
                            i
                            (type)
                            (abs
                              o
                              (type)
                              (lam
                                l
                                [[TxConstraints i] o]
                                (lam
                                  r
                                  [[TxConstraints i] o]
                                  [
                                    [
                                      [
                                        { { TxConstraints i } o }
                                        [
                                          {
                                            [
                                              { { TxConstraints_match i } o } l
                                            ]
                                            [List TxConstraint]
                                          }
                                          (lam
                                            ds
                                            [List TxConstraint]
                                            (lam
                                              ds
                                              [List [InputConstraint i]]
                                              (lam
                                                ds
                                                [List [OutputConstraint o]]
                                                [
                                                  [
                                                    [
                                                      {
                                                        { foldr TxConstraint }
                                                        [List TxConstraint]
                                                      }
                                                      { Cons TxConstraint }
                                                    ]
                                                    [
                                                      {
                                                        [
                                                          {
                                                            {
                                                              TxConstraints_match
                                                              i
                                                            }
                                                            o
                                                          }
                                                          r
                                                        ]
                                                        [List TxConstraint]
                                                      }
                                                      (lam
                                                        ds
                                                        [List TxConstraint]
                                                        (lam
                                                          ds
                                                          [List [InputConstraint i]]
                                                          (lam
                                                            ds
                                                            [List [OutputConstraint o]]
                                                            ds
                                                          )
                                                        )
                                                      )
                                                    ]
                                                  ]
                                                  ds
                                                ]
                                              )
                                            )
                                          )
                                        ]
                                      ]
                                      [
                                        {
                                          [ { { TxConstraints_match i } o } l ]
                                          [List [InputConstraint i]]
                                        }
                                        (lam
                                          ds
                                          [List TxConstraint]
                                          (lam
                                            ds
                                            [List [InputConstraint i]]
                                            (lam
                                              ds
                                              [List [OutputConstraint o]]
                                              [
                                                [
                                                  [
                                                    {
                                                      {
                                                        foldr
                                                        [InputConstraint i]
                                                      }
                                                      [List [InputConstraint i]]
                                                    }
                                                    { Cons [InputConstraint i] }
                                                  ]
                                                  [
                                                    {
                                                      [
                                                        {
                                                          {
                                                            TxConstraints_match
                                                            i
                                                          }
                                                          o
                                                        }
                                                        r
                                                      ]
                                                      [List [InputConstraint i]]
                                                    }
                                                    (lam
                                                      ds
                                                      [List TxConstraint]
                                                      (lam
                                                        ds
                                                        [List [InputConstraint i]]
                                                        (lam
                                                          ds
                                                          [List [OutputConstraint o]]
                                                          ds
                                                        )
                                                      )
                                                    )
                                                  ]
                                                ]
                                                ds
                                              ]
                                            )
                                          )
                                        )
                                      ]
                                    ]
                                    [
                                      {
                                        [ { { TxConstraints_match i } o } l ]
                                        [List [OutputConstraint o]]
                                      }
                                      (lam
                                        ds
                                        [List TxConstraint]
                                        (lam
                                          ds
                                          [List [InputConstraint i]]
                                          (lam
                                            ds
                                            [List [OutputConstraint o]]
                                            [
                                              [
                                                [
                                                  {
                                                    {
                                                      foldr [OutputConstraint o]
                                                    }
                                                    [List [OutputConstraint o]]
                                                  }
                                                  { Cons [OutputConstraint o] }
                                                ]
                                                [
                                                  {
                                                    [
                                                      {
                                                        {
                                                          TxConstraints_match i
                                                        }
                                                        o
                                                      }
                                                      r
                                                    ]
                                                    [List [OutputConstraint o]]
                                                  }
                                                  (lam
                                                    ds
                                                    [List TxConstraint]
                                                    (lam
                                                      ds
                                                      [List [InputConstraint i]]
                                                      (lam
                                                        ds
                                                        [List [OutputConstraint o]]
                                                        ds
                                                      )
                                                    )
                                                  )
                                                ]
                                              ]
                                              ds
                                            ]
                                          )
                                        )
                                      )
                                    ]
                                  ]
                                )
                              )
                            )
                          )
                        )
                        (datatypebind
                          (datatype
                            (tyvardecl FutureAccounts (type))

                            FutureAccounts_match
                            (vardecl
                              FutureAccounts
                              (fun [[Tuple2 (con bytestring)] (con bytestring)] (fun (con bytestring) (fun [[Tuple2 (con bytestring)] (con bytestring)] (fun (con bytestring) FutureAccounts))))
                            )
                          )
                        )
                        (datatypebind
                          (datatype
                            (tyvardecl Payouts (type))

                            Payouts_match
                            (vardecl
                              Payouts
                              (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] Payouts))
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
                            mustPayToOtherScript
                            (all i (type) (all o (type) (fun (con bytestring) (fun (con data) (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] [[TxConstraints i] o])))))
                          )
                          (abs
                            i
                            (type)
                            (abs
                              o
                              (type)
                              (lam
                                vh
                                (con bytestring)
                                (lam
                                  dv
                                  (con data)
                                  (lam
                                    vl
                                    [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                    [
                                      [
                                        [
                                          { { TxConstraints i } o }
                                          [
                                            [
                                              [
                                                {
                                                  { foldr TxConstraint }
                                                  [List TxConstraint]
                                                }
                                                { Cons TxConstraint }
                                              ]
                                              [
                                                { build TxConstraint }
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
                                                            MustIncludeDatum dv
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
                                              { build TxConstraint }
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
                                                            [
                                                              MustPayToOtherScript
                                                              vh
                                                            ]
                                                            dv
                                                          ]
                                                          vl
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
                                                { foldr [InputConstraint i] }
                                                [List [InputConstraint i]]
                                              }
                                              { Cons [InputConstraint i] }
                                            ]
                                            { Nil [InputConstraint i] }
                                          ]
                                          { Nil [InputConstraint i] }
                                        ]
                                      ]
                                      [
                                        [
                                          [
                                            {
                                              { foldr [OutputConstraint o] }
                                              [List [OutputConstraint o]]
                                            }
                                            { Cons [OutputConstraint o] }
                                          ]
                                          { Nil [OutputConstraint o] }
                                        ]
                                        { Nil [OutputConstraint o] }
                                      ]
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
                            fToDataUnit_ctoBuiltinData (fun Unit (con data))
                          )
                          (lam
                            ds
                            Unit
                            [
                              { [ Unit_match ds ] (con data) }
                              [
                                [ (builtin constrData) (con integer 0) ]
                                [ (builtin mkNilData) (con unit ()) ]
                              ]
                            ]
                          )
                        )
                        (termbind
                          (nonstrict)
                          (vardecl unitDatum (con data))
                          [ fToDataUnit_ctoBuiltinData Unit ]
                        )
                        (termbind
                          (strict)
                          (vardecl
                            payoutsTx
                            (fun Payouts (fun FutureAccounts [[TxConstraints Void] Void]))
                          )
                          (lam
                            ds
                            Payouts
                            (lam
                              ds
                              FutureAccounts
                              [
                                {
                                  [ Payouts_match ds ]
                                  [[TxConstraints Void] Void]
                                }
                                (lam
                                  ds
                                  [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                  (lam
                                    ds
                                    [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                    [
                                      {
                                        [ FutureAccounts_match ds ]
                                        [[TxConstraints Void] Void]
                                      }
                                      (lam
                                        ds
                                        [[Tuple2 (con bytestring)] (con bytestring)]
                                        (lam
                                          ds
                                          (con bytestring)
                                          (lam
                                            ds
                                            [[Tuple2 (con bytestring)] (con bytestring)]
                                            (lam
                                              ds
                                              (con bytestring)
                                              [
                                                [
                                                  {
                                                    {
                                                      fMonoidTxConstraints_c
                                                      Void
                                                    }
                                                    Void
                                                  }
                                                  [
                                                    [
                                                      [
                                                        {
                                                          {
                                                            mustPayToOtherScript
                                                            Void
                                                          }
                                                          Void
                                                        }
                                                        ds
                                                      ]
                                                      unitDatum
                                                    ]
                                                    ds
                                                  ]
                                                ]
                                                [
                                                  [
                                                    [
                                                      {
                                                        {
                                                          mustPayToOtherScript
                                                          Void
                                                        }
                                                        Void
                                                      }
                                                      ds
                                                    ]
                                                    unitDatum
                                                  ]
                                                  ds
                                                ]
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
                        (termbind
                          (strict)
                          (vardecl
                            fAdditiveMonoidValue
                            (fun [(lam a (type) a) [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]] (fun [(lam a (type) a) [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]))
                          )
                          (lam
                            ds
                            [(lam a (type) a) [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                            (lam
                              ds
                              [(lam a (type) a) [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                              [ [ [ unionWith addInteger ] ds ] ds ]
                            )
                          )
                        )
                        (datatypebind
                          (datatype
                            (tyvardecl Margins (type))

                            Margins_match
                            (vardecl
                              Margins
                              (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] Margins))
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
                                  [
                                    { { TxConstraints i } o }
                                    { Nil TxConstraint }
                                  ]
                                  { Nil [InputConstraint i] }
                                ]
                                { Nil [OutputConstraint o] }
                              ]
                            )
                          )
                        )
                        (datatypebind
                          (datatype
                            (tyvardecl Observation (fun (type) (type)))
                            (tyvardecl a (type))
                            Observation_match
                            (vardecl
                              Observation
                              (fun a (fun (con integer) [Observation a]))
                            )
                          )
                        )
                        (datatypebind
                          (datatype
                            (tyvardecl SignedMessage (fun (type) (type)))
                            (tyvardecl a (type))
                            SignedMessage_match
                            (vardecl
                              SignedMessage
                              (fun (con bytestring) (fun (con bytestring) (fun (con data) [SignedMessage a])))
                            )
                          )
                        )
                        (datatypebind
                          (datatype
                            (tyvardecl Role (type))

                            Role_match
                            (vardecl Long Role) (vardecl Short Role)
                          )
                        )
                        (datatypebind
                          (datatype
                            (tyvardecl FutureAction (type))

                            FutureAction_match
                            (vardecl
                              AdjustMargin
                              (fun Role (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] FutureAction))
                            )
                            (vardecl
                              Settle
                              (fun [SignedMessage [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]] FutureAction)
                            )
                            (vardecl
                              SettleEarly
                              (fun [SignedMessage [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]] FutureAction)
                            )
                          )
                        )
                        (datatypebind
                          (datatype
                            (tyvardecl FutureState (type))

                            FutureState_match
                            (vardecl Finished FutureState)
                            (vardecl Running (fun Margins FutureState))
                          )
                        )
                        (termbind
                          (strict)
                          (vardecl
                            adjustMargin
                            (fun Role (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun Margins Margins)))
                          )
                          (lam
                            role
                            Role
                            (lam
                              value
                              [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                              (lam
                                accounts
                                Margins
                                {
                                  [
                                    [
                                      {
                                        [ Role_match role ]
                                        (all dead (type) Margins)
                                      }
                                      (abs
                                        dead
                                        (type)
                                        [
                                          { [ Margins_match accounts ] Margins }
                                          (lam
                                            ds
                                            [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                            (lam
                                              ds
                                              [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                              [
                                                [ Margins ds ]
                                                [
                                                  [
                                                    [ unionWith addInteger ] ds
                                                  ]
                                                  value
                                                ]
                                              ]
                                            )
                                          )
                                        ]
                                      )
                                    ]
                                    (abs
                                      dead
                                      (type)
                                      [
                                        { [ Margins_match accounts ] Margins }
                                        (lam
                                          ds
                                          [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                          (lam
                                            ds
                                            [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                            [
                                              [
                                                Margins
                                                [
                                                  [
                                                    [ unionWith addInteger ] ds
                                                  ]
                                                  value
                                                ]
                                              ]
                                              ds
                                            ]
                                          )
                                        )
                                      ]
                                    )
                                  ]
                                  (all dead (type) dead)
                                }
                              )
                            )
                          )
                        )
                        (termbind
                          (strict)
                          (vardecl from (all a (type) (fun a [Interval a])))
                          (abs
                            a
                            (type)
                            (lam
                              s
                              a
                              [
                                [
                                  { Interval a }
                                  [
                                    [ { LowerBound a } [ { Finite a } s ] ] True
                                  ]
                                ]
                                [ [ { UpperBound a } { PosInf a } ] True ]
                              ]
                            )
                          )
                        )
                        (termbind
                          (strict)
                          (vardecl
                            fFromDataInteger_cfromBuiltinData
                            (fun (con data) [Maybe (con integer)])
                          )
                          (lam
                            d
                            (con data)
                            [
                              [
                                [
                                  [
                                    [
                                      [
                                        [
                                          {
                                            (builtin chooseData)
                                            (fun Unit [Maybe (con integer)])
                                          }
                                          d
                                        ]
                                        (lam ds Unit { Nothing (con integer) })
                                      ]
                                      (lam ds Unit { Nothing (con integer) })
                                    ]
                                    (lam ds Unit { Nothing (con integer) })
                                  ]
                                  (lam
                                    ds
                                    Unit
                                    [
                                      { Just (con integer) }
                                      [ (builtin unIData) d ]
                                    ]
                                  )
                                ]
                                (lam ds Unit { Nothing (con integer) })
                              ]
                              Unit
                            ]
                          )
                        )
                        (termbind
                          (strict)
                          (vardecl
                            fFromDataObservation_cfromBuiltinData
                            (all a (type) (fun [(lam a (type) (fun (con data) [Maybe a])) a] (fun (con data) [Maybe [Observation a]])))
                          )
                          (abs
                            a
                            (type)
                            (lam
                              dFromData
                              [(lam a (type) (fun (con data) [Maybe a])) a]
                              (lam
                                d
                                (con data)
                                [
                                  [
                                    [
                                      [
                                        [
                                          [
                                            [
                                              {
                                                (builtin chooseData)
                                                (fun Unit [Maybe [Observation a]])
                                              }
                                              d
                                            ]
                                            (lam
                                              ds
                                              Unit
                                              (let
                                                (nonrec)
                                                (termbind
                                                  (nonstrict)
                                                  (vardecl
                                                    tup
                                                    [[(con pair) (con integer)] [(con list) (con data)]]
                                                  )
                                                  [ (builtin unConstrData) d ]
                                                )
                                                (termbind
                                                  (nonstrict)
                                                  (vardecl
                                                    l [(con list) (con data)]
                                                  )
                                                  [
                                                    {
                                                      {
                                                        (builtin sndPair)
                                                        (con integer)
                                                      }
                                                      [(con list) (con data)]
                                                    }
                                                    tup
                                                  ]
                                                )
                                                (termbind
                                                  (nonstrict)
                                                  (vardecl
                                                    l [(con list) (con data)]
                                                  )
                                                  [
                                                    {
                                                      (builtin tailList)
                                                      (con data)
                                                    }
                                                    l
                                                  ]
                                                )
                                                (termbind
                                                  (nonstrict)
                                                  (vardecl
                                                    nilCase
                                                    [Maybe [Observation a]]
                                                  )
                                                  {
                                                    [
                                                      [
                                                        {
                                                          [
                                                            { Maybe_match a }
                                                            [
                                                              dFromData
                                                              [
                                                                {
                                                                  (builtin
                                                                    headList
                                                                  )
                                                                  (con data)
                                                                }
                                                                l
                                                              ]
                                                            ]
                                                          ]
                                                          (all dead (type) [Maybe [Observation a]])
                                                        }
                                                        (lam
                                                          ipv
                                                          a
                                                          (abs
                                                            dead
                                                            (type)
                                                            {
                                                              [
                                                                [
                                                                  {
                                                                    [
                                                                      {
                                                                        Maybe_match
                                                                        (con integer)
                                                                      }
                                                                      [
                                                                        fFromDataInteger_cfromBuiltinData
                                                                        [
                                                                          {
                                                                            (builtin
                                                                              headList
                                                                            )
                                                                            (con data)
                                                                          }
                                                                          l
                                                                        ]
                                                                      ]
                                                                    ]
                                                                    (all dead (type) [Maybe [Observation a]])
                                                                  }
                                                                  (lam
                                                                    ipv
                                                                    (con integer)
                                                                    (abs
                                                                      dead
                                                                      (type)
                                                                      [
                                                                        {
                                                                          Just
                                                                          [Observation a]
                                                                        }
                                                                        [
                                                                          [
                                                                            {
                                                                              Observation
                                                                              a
                                                                            }
                                                                            ipv
                                                                          ]
                                                                          ipv
                                                                        ]
                                                                      ]
                                                                    )
                                                                  )
                                                                ]
                                                                (abs
                                                                  dead
                                                                  (type)
                                                                  {
                                                                    Nothing
                                                                    [Observation a]
                                                                  }
                                                                )
                                                              ]
                                                              (all dead (type) dead)
                                                            }
                                                          )
                                                        )
                                                      ]
                                                      (abs
                                                        dead
                                                        (type)
                                                        {
                                                          Nothing
                                                          [Observation a]
                                                        }
                                                      )
                                                    ]
                                                    (all dead (type) dead)
                                                  }
                                                )
                                                (termbind
                                                  (nonstrict)
                                                  (vardecl
                                                    lvl [Maybe [Observation a]]
                                                  )
                                                  [
                                                    [
                                                      [
                                                        [
                                                          {
                                                            {
                                                              (builtin
                                                                chooseList
                                                              )
                                                              (con data)
                                                            }
                                                            (fun Unit [Maybe [Observation a]])
                                                          }
                                                          [
                                                            {
                                                              (builtin tailList)
                                                              (con data)
                                                            }
                                                            l
                                                          ]
                                                        ]
                                                        (lam ds Unit nilCase)
                                                      ]
                                                      (lam
                                                        ds
                                                        Unit
                                                        {
                                                          Nothing
                                                          [Observation a]
                                                        }
                                                      )
                                                    ]
                                                    Unit
                                                  ]
                                                )
                                                (termbind
                                                  (nonstrict)
                                                  (vardecl
                                                    lvl [Maybe [Observation a]]
                                                  )
                                                  [
                                                    [
                                                      [
                                                        [
                                                          {
                                                            {
                                                              (builtin
                                                                chooseList
                                                              )
                                                              (con data)
                                                            }
                                                            (fun Unit [Maybe [Observation a]])
                                                          }
                                                          l
                                                        ]
                                                        (lam
                                                          ds
                                                          Unit
                                                          {
                                                            Nothing
                                                            [Observation a]
                                                          }
                                                        )
                                                      ]
                                                      (lam ds Unit lvl)
                                                    ]
                                                    Unit
                                                  ]
                                                )
                                                (termbind
                                                  (nonstrict)
                                                  (vardecl
                                                    x [Maybe [Observation a]]
                                                  )
                                                  [
                                                    [
                                                      [
                                                        [
                                                          {
                                                            {
                                                              (builtin
                                                                chooseList
                                                              )
                                                              (con data)
                                                            }
                                                            (fun Unit [Maybe [Observation a]])
                                                          }
                                                          l
                                                        ]
                                                        (lam
                                                          ds
                                                          Unit
                                                          {
                                                            Nothing
                                                            [Observation a]
                                                          }
                                                        )
                                                      ]
                                                      (lam ds Unit lvl)
                                                    ]
                                                    Unit
                                                  ]
                                                )
                                                [
                                                  [
                                                    [
                                                      [
                                                        {
                                                          (builtin ifThenElse)
                                                          (fun (con unit) [Maybe [Observation a]])
                                                        }
                                                        [
                                                          [
                                                            (builtin
                                                              equalsInteger
                                                            )
                                                            [
                                                              {
                                                                {
                                                                  (builtin
                                                                    fstPair
                                                                  )
                                                                  (con integer)
                                                                }
                                                                [(con list) (con data)]
                                                              }
                                                              tup
                                                            ]
                                                          ]
                                                          (con integer 0)
                                                        ]
                                                      ]
                                                      (lam ds (con unit) x)
                                                    ]
                                                    (lam
                                                      ds
                                                      (con unit)
                                                      {
                                                        Nothing [Observation a]
                                                      }
                                                    )
                                                  ]
                                                  (con unit ())
                                                ]
                                              )
                                            )
                                          ]
                                          (lam
                                            ds Unit { Nothing [Observation a] }
                                          )
                                        ]
                                        (lam ds Unit { Nothing [Observation a] }
                                        )
                                      ]
                                      (lam ds Unit { Nothing [Observation a] })
                                    ]
                                    (lam ds Unit { Nothing [Observation a] })
                                  ]
                                  Unit
                                ]
                              )
                            )
                          )
                        )
                        (termbind
                          (strict)
                          (vardecl
                            fFromDataBuiltinByteString_cfromBuiltinData
                            (fun (con data) [Maybe (con bytestring)])
                          )
                          (lam
                            d
                            (con data)
                            [
                              [
                                [
                                  [
                                    [
                                      [
                                        [
                                          {
                                            (builtin chooseData)
                                            (fun Unit [Maybe (con bytestring)])
                                          }
                                          d
                                        ]
                                        (lam
                                          ds Unit { Nothing (con bytestring) }
                                        )
                                      ]
                                      (lam ds Unit { Nothing (con bytestring) })
                                    ]
                                    (lam ds Unit { Nothing (con bytestring) })
                                  ]
                                  (lam ds Unit { Nothing (con bytestring) })
                                ]
                                (lam
                                  ds
                                  Unit
                                  [
                                    { Just (con bytestring) }
                                    [ (builtin unBData) d ]
                                  ]
                                )
                              ]
                              Unit
                            ]
                          )
                        )
                        (termbind
                          (strict)
                          (vardecl
                            fFromDataMap
                            (all v (type) (all k (type) (fun Unit [Maybe [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) k] v]])))
                          )
                          (abs
                            v
                            (type)
                            (abs
                              k
                              (type)
                              (lam
                                ds
                                Unit
                                {
                                  Nothing
                                  [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) k] v]
                                }
                              )
                            )
                          )
                        )
                        (termbind
                          (strict)
                          (vardecl
                            fFromDataMap_cfromBuiltinData
                            (all k (type) (all v (type) (fun [(lam a (type) (fun (con data) [Maybe a])) k] (fun [(lam a (type) (fun (con data) [Maybe a])) v] (fun (con data) [Maybe [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) k] v]])))))
                          )
                          (abs
                            k
                            (type)
                            (abs
                              v
                              (type)
                              (lam
                                dFromData
                                [(lam a (type) (fun (con data) [Maybe a])) k]
                                (lam
                                  dFromData
                                  [(lam a (type) (fun (con data) [Maybe a])) v]
                                  (lam
                                    d
                                    (con data)
                                    (let
                                      (rec)
                                      (termbind
                                        (strict)
                                        (vardecl
                                          go
                                          (fun [(con list) [[(con pair) (con data)] (con data)]] [Maybe [List [[Tuple2 k] v]]])
                                        )
                                        (lam
                                          l
                                          [(con list) [[(con pair) (con data)] (con data)]]
                                          (let
                                            (nonrec)
                                            (termbind
                                              (nonstrict)
                                              (vardecl
                                                tup
                                                [[(con pair) (con data)] (con data)]
                                              )
                                              [
                                                {
                                                  (builtin headList)
                                                  [[(con pair) (con data)] (con data)]
                                                }
                                                l
                                              ]
                                            )
                                            (termbind
                                              (nonstrict)
                                              (vardecl
                                                lvl
                                                [Maybe [List [[Tuple2 k] v]]]
                                              )
                                              {
                                                [
                                                  [
                                                    {
                                                      [
                                                        { Maybe_match k }
                                                        [
                                                          dFromData
                                                          [
                                                            {
                                                              {
                                                                (builtin fstPair
                                                                )
                                                                (con data)
                                                              }
                                                              (con data)
                                                            }
                                                            tup
                                                          ]
                                                        ]
                                                      ]
                                                      (all dead (type) [Maybe [List [[Tuple2 k] v]]])
                                                    }
                                                    (lam
                                                      a
                                                      k
                                                      (abs
                                                        dead
                                                        (type)
                                                        {
                                                          [
                                                            [
                                                              {
                                                                [
                                                                  {
                                                                    Maybe_match
                                                                    v
                                                                  }
                                                                  [
                                                                    dFromData
                                                                    [
                                                                      {
                                                                        {
                                                                          (builtin
                                                                            sndPair
                                                                          )
                                                                          (con data)
                                                                        }
                                                                        (con data)
                                                                      }
                                                                      tup
                                                                    ]
                                                                  ]
                                                                ]
                                                                (all dead (type) [Maybe [List [[Tuple2 k] v]]])
                                                              }
                                                              (lam
                                                                ipv
                                                                v
                                                                (abs
                                                                  dead
                                                                  (type)
                                                                  {
                                                                    [
                                                                      [
                                                                        {
                                                                          [
                                                                            {
                                                                              Maybe_match
                                                                              [List [[Tuple2 k] v]]
                                                                            }
                                                                            [
                                                                              go
                                                                              [
                                                                                {
                                                                                  (builtin
                                                                                    tailList
                                                                                  )
                                                                                  [[(con pair) (con data)] (con data)]
                                                                                }
                                                                                l
                                                                              ]
                                                                            ]
                                                                          ]
                                                                          (all dead (type) [Maybe [List [[Tuple2 k] v]]])
                                                                        }
                                                                        (lam
                                                                          ipv
                                                                          [List [[Tuple2 k] v]]
                                                                          (abs
                                                                            dead
                                                                            (type)
                                                                            [
                                                                              {
                                                                                Just
                                                                                [List [[Tuple2 k] v]]
                                                                              }
                                                                              [
                                                                                [
                                                                                  {
                                                                                    Cons
                                                                                    [[Tuple2 k] v]
                                                                                  }
                                                                                  [
                                                                                    [
                                                                                      {
                                                                                        {
                                                                                          Tuple2
                                                                                          k
                                                                                        }
                                                                                        v
                                                                                      }
                                                                                      a
                                                                                    ]
                                                                                    ipv
                                                                                  ]
                                                                                ]
                                                                                ipv
                                                                              ]
                                                                            ]
                                                                          )
                                                                        )
                                                                      ]
                                                                      (abs
                                                                        dead
                                                                        (type)
                                                                        {
                                                                          Nothing
                                                                          [List [[Tuple2 k] v]]
                                                                        }
                                                                      )
                                                                    ]
                                                                    (all dead (type) dead)
                                                                  }
                                                                )
                                                              )
                                                            ]
                                                            (abs
                                                              dead
                                                              (type)
                                                              {
                                                                Nothing
                                                                [List [[Tuple2 k] v]]
                                                              }
                                                            )
                                                          ]
                                                          (all dead (type) dead)
                                                        }
                                                      )
                                                    )
                                                  ]
                                                  (abs
                                                    dead
                                                    (type)
                                                    {
                                                      Nothing
                                                      [List [[Tuple2 k] v]]
                                                    }
                                                  )
                                                ]
                                                (all dead (type) dead)
                                              }
                                            )
                                            [
                                              [
                                                [
                                                  [
                                                    {
                                                      {
                                                        (builtin chooseList)
                                                        [[(con pair) (con data)] (con data)]
                                                      }
                                                      (fun Unit [Maybe [List [[Tuple2 k] v]]])
                                                    }
                                                    l
                                                  ]
                                                  { { fFromDataMap v } k }
                                                ]
                                                (lam ds Unit lvl)
                                              ]
                                              Unit
                                            ]
                                          )
                                        )
                                      )
                                      (let
                                        (nonrec)
                                        (termbind
                                          (nonstrict)
                                          (vardecl
                                            lvl
                                            [Maybe [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) k] v]]
                                          )
                                          {
                                            [
                                              [
                                                {
                                                  [
                                                    {
                                                      Maybe_match
                                                      [List [[Tuple2 k] v]]
                                                    }
                                                    [
                                                      go
                                                      [ (builtin unMapData) d ]
                                                    ]
                                                  ]
                                                  (all dead (type) [Maybe [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) k] v]])
                                                }
                                                (lam
                                                  a
                                                  [List [[Tuple2 k] v]]
                                                  (abs
                                                    dead
                                                    (type)
                                                    [
                                                      {
                                                        Just
                                                        [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) k] v]
                                                      }
                                                      a
                                                    ]
                                                  )
                                                )
                                              ]
                                              (abs
                                                dead
                                                (type)
                                                {
                                                  Nothing
                                                  [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) k] v]
                                                }
                                              )
                                            ]
                                            (all dead (type) dead)
                                          }
                                        )
                                        [
                                          [
                                            [
                                              [
                                                [
                                                  [
                                                    [
                                                      {
                                                        (builtin chooseData)
                                                        (fun Unit [Maybe [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) k] v]])
                                                      }
                                                      d
                                                    ]
                                                    { { fFromDataMap v } k }
                                                  ]
                                                  (lam ds Unit lvl)
                                                ]
                                                { { fFromDataMap v } k }
                                              ]
                                              { { fFromDataMap v } k }
                                            ]
                                            { { fFromDataMap v } k }
                                          ]
                                          Unit
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
                          (nonstrict)
                          (vardecl
                            fFromDataValue
                            (fun (con data) [Maybe [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]])
                          )
                          [
                            [
                              {
                                {
                                  fFromDataMap_cfromBuiltinData (con bytestring)
                                }
                                (con integer)
                              }
                              fFromDataBuiltinByteString_cfromBuiltinData
                            ]
                            fFromDataInteger_cfromBuiltinData
                          ]
                        )
                        (termbind
                          (nonstrict)
                          (vardecl
                            fFromDataValue
                            (fun (con data) [Maybe [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]])
                          )
                          [
                            [
                              {
                                {
                                  fFromDataMap_cfromBuiltinData (con bytestring)
                                }
                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]
                              }
                              fFromDataBuiltinByteString_cfromBuiltinData
                            ]
                            fFromDataValue
                          ]
                        )
                        (termbind
                          (nonstrict)
                          (vardecl
                            futureStateMachine
                            (fun (con data) [Maybe [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]])
                          )
                          [
                            {
                              fFromDataObservation_cfromBuiltinData
                              [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                            }
                            fFromDataValue
                          ]
                        )
                        (termbind
                          (strict)
                          (vardecl
                            totalMargin
                            (fun Margins [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]])
                          )
                          (lam
                            ds
                            Margins
                            [
                              {
                                [ Margins_match ds ]
                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                              }
                              (lam
                                ds
                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                (lam
                                  ds
                                  [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                  [ [ fAdditiveMonoidValue ds ] ds ]
                                )
                              )
                            ]
                          )
                        )
                        (datatypebind
                          (datatype
                            (tyvardecl Either (fun (type) (fun (type) (type))))
                            (tyvardecl a (type)) (tyvardecl b (type))
                            Either_match
                            (vardecl Left (fun a [[Either a] b]))
                            (vardecl Right (fun b [[Either a] b]))
                          )
                        )
                        (datatypebind
                          (datatype
                            (tyvardecl SignedMessageCheckError (type))

                            SignedMessageCheckError_match
                            (vardecl
                              DatumMissing
                              (fun (con bytestring) SignedMessageCheckError)
                            )
                            (vardecl
                              DatumNotEqualToExpected SignedMessageCheckError
                            )
                            (vardecl DecodingError SignedMessageCheckError)
                            (vardecl
                              SignatureMismatch
                              (fun (con bytestring) (fun (con bytestring) (fun (con bytestring) SignedMessageCheckError)))
                            )
                          )
                        )
                        (termbind
                          (strict)
                          (vardecl
                            mustHashDatum
                            (all i (type) (all o (type) (fun (con bytestring) (fun (con data) [[TxConstraints i] o]))))
                          )
                          (abs
                            i
                            (type)
                            (abs
                              o
                              (type)
                              (lam
                                dvh
                                (con bytestring)
                                (lam
                                  x
                                  (con data)
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
                                              (lam
                                                n
                                                a
                                                [
                                                  [
                                                    c
                                                    [ [ MustHashDatum dvh ] x ]
                                                  ]
                                                  n
                                                ]
                                              )
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
                        )
                        (termbind
                          (strict)
                          (vardecl
                            checkHashConstraints
                            (all a (type) (all i (type) (all o (type) (fun [(lam a (type) (fun (con data) [Maybe a])) a] (fun [SignedMessage a] [[Either SignedMessageCheckError] [[Tuple2 a] [[TxConstraints i] o]]])))))
                          )
                          (abs
                            a
                            (type)
                            (abs
                              i
                              (type)
                              (abs
                                o
                                (type)
                                (lam
                                  dFromData
                                  [(lam a (type) (fun (con data) [Maybe a])) a]
                                  (lam
                                    ds
                                    [SignedMessage a]
                                    [
                                      {
                                        [ { SignedMessage_match a } ds ]
                                        [[Either SignedMessageCheckError] [[Tuple2 a] [[TxConstraints i] o]]]
                                      }
                                      (lam
                                        ds
                                        (con bytestring)
                                        (lam
                                          ds
                                          (con bytestring)
                                          (lam
                                            ds
                                            (con data)
                                            {
                                              [
                                                [
                                                  {
                                                    [
                                                      { Maybe_match a }
                                                      [ dFromData ds ]
                                                    ]
                                                    (all dead (type) [[Either SignedMessageCheckError] [[Tuple2 a] [[TxConstraints i] o]]])
                                                  }
                                                  (lam
                                                    a
                                                    a
                                                    (abs
                                                      dead
                                                      (type)
                                                      [
                                                        {
                                                          {
                                                            Right
                                                            SignedMessageCheckError
                                                          }
                                                          [[Tuple2 a] [[TxConstraints i] o]]
                                                        }
                                                        [
                                                          [
                                                            {
                                                              { Tuple2 a }
                                                              [[TxConstraints i] o]
                                                            }
                                                            a
                                                          ]
                                                          [
                                                            [
                                                              {
                                                                {
                                                                  mustHashDatum
                                                                  i
                                                                }
                                                                o
                                                              }
                                                              ds
                                                            ]
                                                            ds
                                                          ]
                                                        ]
                                                      ]
                                                    )
                                                  )
                                                ]
                                                (abs
                                                  dead
                                                  (type)
                                                  [
                                                    [
                                                      {
                                                        (builtin trace)
                                                        [[Either SignedMessageCheckError] [[Tuple2 a] [[TxConstraints i] o]]]
                                                      }
                                                      (con string "Li")
                                                    ]
                                                    [
                                                      {
                                                        {
                                                          Left
                                                          SignedMessageCheckError
                                                        }
                                                        [[Tuple2 a] [[TxConstraints i] o]]
                                                      }
                                                      DecodingError
                                                    ]
                                                  ]
                                                )
                                              ]
                                              (all dead (type) dead)
                                            }
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
                            verifySignedMessageConstraints
                            (all a (type) (all i (type) (all o (type) (fun [(lam a (type) (fun (con data) [Maybe a])) a] (fun (con bytestring) (fun [SignedMessage a] [[Either SignedMessageCheckError] [[Tuple2 a] [[TxConstraints i] o]]]))))))
                          )
                          (abs
                            a
                            (type)
                            (abs
                              i
                              (type)
                              (abs
                                o
                                (type)
                                (lam
                                  dFromData
                                  [(lam a (type) (fun (con data) [Maybe a])) a]
                                  (lam
                                    pk
                                    (con bytestring)
                                    (lam
                                      s
                                      [SignedMessage a]
                                      [
                                        {
                                          [ { SignedMessage_match a } s ]
                                          [[Either SignedMessageCheckError] [[Tuple2 a] [[TxConstraints i] o]]]
                                        }
                                        (lam
                                          ds
                                          (con bytestring)
                                          (lam
                                            ds
                                            (con bytestring)
                                            (lam
                                              ds
                                              (con data)
                                              {
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
                                                                  [
                                                                    (builtin
                                                                      verifySignature
                                                                    )
                                                                    pk
                                                                  ]
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
                                                      (all dead (type) [[Either SignedMessageCheckError] [[Tuple2 a] [[TxConstraints i] o]]])
                                                    }
                                                    (abs
                                                      dead
                                                      (type)
                                                      [
                                                        [
                                                          {
                                                            {
                                                              {
                                                                checkHashConstraints
                                                                a
                                                              }
                                                              i
                                                            }
                                                            o
                                                          }
                                                          dFromData
                                                        ]
                                                        s
                                                      ]
                                                    )
                                                  ]
                                                  (abs
                                                    dead
                                                    (type)
                                                    [
                                                      {
                                                        {
                                                          Left
                                                          SignedMessageCheckError
                                                        }
                                                        [[Tuple2 a] [[TxConstraints i] o]]
                                                      }
                                                      [
                                                        [
                                                          [
                                                            SignatureMismatch ds
                                                          ]
                                                          pk
                                                        ]
                                                        ds
                                                      ]
                                                    ]
                                                  )
                                                ]
                                                (all dead (type) dead)
                                              }
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
                        (datatypebind
                          (datatype
                            (tyvardecl Future (type))

                            Future_match
                            (vardecl
                              Future
                              (fun (con integer) (fun (con integer) (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun (con bytestring) (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] Future))))))
                            )
                          )
                        )
                        (termbind
                          (strict)
                          (vardecl
                            requiredMargin
                            (fun Future (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]))
                          )
                          (lam
                            ds
                            Future
                            (lam
                              spotPrice
                              [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                              [
                                {
                                  [ Future_match ds ]
                                  [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                }
                                (lam
                                  ds
                                  (con integer)
                                  (lam
                                    ds
                                    (con integer)
                                    (lam
                                      ds
                                      [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                      (lam
                                        ds
                                        [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                        (lam
                                          ds
                                          (con bytestring)
                                          (lam
                                            ds
                                            [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                            [
                                              [ [ unionWith addInteger ] ds ]
                                              [
                                                [
                                                  fAdditiveGroupValue_cscale ds
                                                ]
                                                [
                                                  [
                                                    fAdditiveGroupValue
                                                    spotPrice
                                                  ]
                                                  ds
                                                ]
                                              ]
                                            ]
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
                                  v
                                  [(lam a (type) (fun a (fun a a))) a]
                                  (lam v a v)
                                )
                              ]
                            )
                          )
                        )
                        (termbind
                          (strict)
                          (vardecl
                            one (all a (type) (fun [MultiplicativeMonoid a] a))
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
                                  v
                                  [(lam a (type) (fun a (fun a a))) a]
                                  (lam v a v)
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
                                        [
                                          [ { p1MultiplicativeMonoid a } v ] eta
                                        ]
                                        eta
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
                              {
                                [
                                  [
                                    { [ Bool_match ds ] (all dead (type) Bool) }
                                    (abs dead (type) x)
                                  ]
                                  (abs dead (type) False)
                                ]
                                (all dead (type) dead)
                              }
                            )
                          )
                        )
                        (termbind
                          (nonstrict)
                          (vardecl
                            fMultiplicativeMonoidBool
                            [MultiplicativeMonoid Bool]
                          )
                          [
                            [ { CConsMultiplicativeMonoid Bool } bad_name ] True
                          ]
                        )
                        (termbind
                          (strict)
                          (vardecl
                            checkPred
                            (fun (fun [[These (con integer)] (con integer)] Bool) (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] Bool)))
                          )
                          (lam
                            f
                            (fun [[These (con integer)] (con integer)] Bool)
                            (lam
                              l
                              [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                              (lam
                                r
                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                (let
                                  (nonrec)
                                  (termbind
                                    (nonstrict)
                                    (vardecl
                                      dMonoid [Monoid [(lam a (type) a) Bool]]
                                    )
                                    [
                                      { fMonoidProduct Bool }
                                      fMultiplicativeMonoidBool
                                    ]
                                  )
                                  [
                                    [
                                      [
                                        {
                                          {
                                            fFoldableNil_cfoldMap
                                            [(lam a (type) a) Bool]
                                          }
                                          [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]]
                                        }
                                        [
                                          { fMonoidProduct Bool }
                                          fMultiplicativeMonoidBool
                                        ]
                                      ]
                                      (lam
                                        ds
                                        [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]]
                                        [
                                          {
                                            [
                                              {
                                                {
                                                  Tuple2_match (con bytestring)
                                                }
                                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]
                                              }
                                              ds
                                            ]
                                            [(lam a (type) a) Bool]
                                          }
                                          (lam
                                            ds
                                            (con bytestring)
                                            (lam
                                              a
                                              [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]
                                              [
                                                [
                                                  [
                                                    {
                                                      {
                                                        fFoldableNil_cfoldMap
                                                        [(lam a (type) a) Bool]
                                                      }
                                                      [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]
                                                    }
                                                    dMonoid
                                                  ]
                                                  (lam
                                                    ds
                                                    [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]
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
                                                        [(lam a (type) a) Bool]
                                                      }
                                                      (lam
                                                        ds
                                                        (con bytestring)
                                                        (lam
                                                          a
                                                          [[These (con integer)] (con integer)]
                                                          [ f a ]
                                                        )
                                                      )
                                                    ]
                                                  )
                                                ]
                                                a
                                              ]
                                            )
                                          )
                                        ]
                                      )
                                    ]
                                    [ [ unionVal l ] r ]
                                  ]
                                )
                              )
                            )
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
                                [
                                  [
                                    [
                                      checkPred
                                      (lam
                                        k
                                        [[These (con integer)] (con integer)]
                                        [
                                          [
                                            [
                                              {
                                                [
                                                  {
                                                    {
                                                      These_match (con integer)
                                                    }
                                                    (con integer)
                                                  }
                                                  k
                                                ]
                                                Bool
                                              }
                                              (lam
                                                b
                                                (con integer)
                                                [ [ f (con integer 0) ] b ]
                                              )
                                            ]
                                            (lam
                                              a
                                              (con integer)
                                              (lam b (con integer) [ [ f a ] b ]
                                              )
                                            )
                                          ]
                                          (lam
                                            a
                                            (con integer)
                                            [ [ f a ] (con integer 0) ]
                                          )
                                        ]
                                      )
                                    ]
                                    l
                                  ]
                                  r
                                ]
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
                              (nonrec)
                              (termbind
                                (nonstrict)
                                (vardecl
                                  dMonoid [Monoid [(lam a (type) a) Bool]]
                                )
                                [
                                  { fMonoidProduct Bool }
                                  fMultiplicativeMonoidBool
                                ]
                              )
                              [
                                [
                                  [
                                    {
                                      {
                                        fFoldableNil_cfoldMap
                                        [(lam a (type) a) Bool]
                                      }
                                      [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                    }
                                    [
                                      { fMonoidProduct Bool }
                                      fMultiplicativeMonoidBool
                                    ]
                                  ]
                                  (lam
                                    ds
                                    [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                    [
                                      {
                                        [
                                          {
                                            { Tuple2_match (con bytestring) }
                                            [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]
                                          }
                                          ds
                                        ]
                                        [(lam a (type) a) Bool]
                                      }
                                      (lam
                                        ds
                                        (con bytestring)
                                        (lam
                                          a
                                          [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]
                                          [
                                            [
                                              [
                                                {
                                                  {
                                                    fFoldableNil_cfoldMap
                                                    [(lam a (type) a) Bool]
                                                  }
                                                  [[Tuple2 (con bytestring)] (con integer)]
                                                }
                                                dMonoid
                                              ]
                                              (lam
                                                ds
                                                [[Tuple2 (con bytestring)] (con integer)]
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
                                                    [(lam a (type) a) Bool]
                                                  }
                                                  (lam
                                                    ds
                                                    (con bytestring)
                                                    (lam
                                                      a
                                                      (con integer)
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
                                                                (con integer 0)
                                                              ]
                                                              a
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
                                            ]
                                            a
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
                        (termbind
                          (strict)
                          (vardecl
                            lt
                            (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] Bool))
                          )
                          (lam
                            l
                            [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                            (lam
                              r
                              [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                              {
                                [
                                  [
                                    {
                                      [ Bool_match [ isZero l ] ]
                                      (all dead (type) Bool)
                                    }
                                    (abs
                                      dead
                                      (type)
                                      {
                                        [
                                          [
                                            {
                                              [ Bool_match [ isZero r ] ]
                                              (all dead (type) Bool)
                                            }
                                            (abs dead (type) False)
                                          ]
                                          (abs
                                            dead
                                            (type)
                                            [
                                              [
                                                [ checkBinRel lessThanInteger ]
                                                l
                                              ]
                                              r
                                            ]
                                          )
                                        ]
                                        (all dead (type) dead)
                                      }
                                    )
                                  ]
                                  (abs
                                    dead
                                    (type)
                                    [ [ [ checkBinRel lessThanInteger ] l ] r ]
                                  )
                                ]
                                (all dead (type) dead)
                              }
                            )
                          )
                        )
                        (termbind
                          (strict)
                          (vardecl
                            violatingRole
                            (fun Future (fun Margins (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] [Maybe Role])))
                          )
                          (lam
                            future
                            Future
                            (lam
                              margins
                              Margins
                              (lam
                                spotPrice
                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                (let
                                  (nonrec)
                                  (termbind
                                    (nonstrict)
                                    (vardecl
                                      minMargin
                                      [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                    )
                                    [ [ requiredMargin future ] spotPrice ]
                                  )
                                  {
                                    [
                                      [
                                        {
                                          [
                                            Bool_match
                                            [
                                              [
                                                lt
                                                [
                                                  {
                                                    [ Margins_match margins ]
                                                    [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                  }
                                                  (lam
                                                    ds
                                                    [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                    (lam
                                                      ds
                                                      [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                      ds
                                                    )
                                                  )
                                                ]
                                              ]
                                              minMargin
                                            ]
                                          ]
                                          (all dead (type) [Maybe Role])
                                        }
                                        (abs dead (type) [ { Just Role } Short ]
                                        )
                                      ]
                                      (abs
                                        dead
                                        (type)
                                        {
                                          [
                                            [
                                              {
                                                [
                                                  Bool_match
                                                  [
                                                    [
                                                      lt
                                                      [
                                                        {
                                                          [
                                                            Margins_match
                                                            margins
                                                          ]
                                                          [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                        }
                                                        (lam
                                                          ds
                                                          [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                          (lam
                                                            ds
                                                            [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                            ds
                                                          )
                                                        )
                                                      ]
                                                    ]
                                                    minMargin
                                                  ]
                                                ]
                                                (all dead (type) [Maybe Role])
                                              }
                                              (abs
                                                dead
                                                (type)
                                                [ { Just Role } Long ]
                                              )
                                            ]
                                            (abs dead (type) { Nothing Role })
                                          ]
                                          (all dead (type) dead)
                                        }
                                      )
                                    ]
                                    (all dead (type) dead)
                                  }
                                )
                              )
                            )
                          )
                        )
                        (termbind
                          (strict)
                          (vardecl
                            transition
                            (fun Future (fun FutureAccounts (fun [State FutureState] (fun FutureAction [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]]))))
                          )
                          (lam
                            future
                            Future
                            (lam
                              owners
                              FutureAccounts
                              (lam
                                ds
                                [State FutureState]
                                (lam
                                  i
                                  FutureAction
                                  [
                                    {
                                      [ Future_match future ]
                                      [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]]
                                    }
                                    (lam
                                      ds
                                      (con integer)
                                      (lam
                                        ds
                                        (con integer)
                                        (lam
                                          ds
                                          [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                          (lam
                                            ds
                                            [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                            (lam
                                              ds
                                              (con bytestring)
                                              (lam
                                                ds
                                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                [
                                                  {
                                                    [
                                                      {
                                                        State_match FutureState
                                                      }
                                                      ds
                                                    ]
                                                    [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]]
                                                  }
                                                  (lam
                                                    ds
                                                    FutureState
                                                    (lam
                                                      ds
                                                      [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                      {
                                                        [
                                                          [
                                                            {
                                                              [
                                                                FutureState_match
                                                                ds
                                                              ]
                                                              (all dead (type) [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]])
                                                            }
                                                            (abs
                                                              dead
                                                              (type)
                                                              {
                                                                Nothing
                                                                [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]
                                                              }
                                                            )
                                                          ]
                                                          (lam
                                                            accounts
                                                            Margins
                                                            (abs
                                                              dead
                                                              (type)
                                                              [
                                                                [
                                                                  [
                                                                    {
                                                                      [
                                                                        FutureAction_match
                                                                        i
                                                                      ]
                                                                      [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]]
                                                                    }
                                                                    (lam
                                                                      role
                                                                      Role
                                                                      (lam
                                                                        topUp
                                                                        [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                        [
                                                                          {
                                                                            Just
                                                                            [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]
                                                                          }
                                                                          [
                                                                            [
                                                                              {
                                                                                {
                                                                                  Tuple2
                                                                                  [[TxConstraints Void] Void]
                                                                                }
                                                                                [State FutureState]
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
                                                                                  FutureState
                                                                                }
                                                                                [
                                                                                  Running
                                                                                  [
                                                                                    [
                                                                                      [
                                                                                        adjustMargin
                                                                                        role
                                                                                      ]
                                                                                      topUp
                                                                                    ]
                                                                                    accounts
                                                                                  ]
                                                                                ]
                                                                              ]
                                                                              [
                                                                                [
                                                                                  [
                                                                                    unionWith
                                                                                    addInteger
                                                                                  ]
                                                                                  topUp
                                                                                ]
                                                                                [
                                                                                  totalMargin
                                                                                  accounts
                                                                                ]
                                                                              ]
                                                                            ]
                                                                          ]
                                                                        ]
                                                                      )
                                                                    )
                                                                  ]
                                                                  (lam
                                                                    ov
                                                                    [SignedMessage [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]]
                                                                    [
                                                                      [
                                                                        {
                                                                          [
                                                                            {
                                                                              {
                                                                                Either_match
                                                                                SignedMessageCheckError
                                                                              }
                                                                              [[Tuple2 [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]] [[TxConstraints Void] Void]]
                                                                            }
                                                                            [
                                                                              [
                                                                                [
                                                                                  {
                                                                                    {
                                                                                      {
                                                                                        verifySignedMessageConstraints
                                                                                        [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                                                      }
                                                                                      Void
                                                                                    }
                                                                                    Void
                                                                                  }
                                                                                  futureStateMachine
                                                                                ]
                                                                                ds
                                                                              ]
                                                                              ov
                                                                            ]
                                                                          ]
                                                                          [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]]
                                                                        }
                                                                        (lam
                                                                          x
                                                                          SignedMessageCheckError
                                                                          {
                                                                            Nothing
                                                                            [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]
                                                                          }
                                                                        )
                                                                      ]
                                                                      (lam
                                                                        y
                                                                        [[Tuple2 [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]] [[TxConstraints Void] Void]]
                                                                        [
                                                                          {
                                                                            [
                                                                              {
                                                                                {
                                                                                  Tuple2_match
                                                                                  [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                                                }
                                                                                [[TxConstraints Void] Void]
                                                                              }
                                                                              y
                                                                            ]
                                                                            [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]]
                                                                          }
                                                                          (lam
                                                                            ds
                                                                            [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                                            (lam
                                                                              oracleConstraints
                                                                              [[TxConstraints Void] Void]
                                                                              [
                                                                                {
                                                                                  [
                                                                                    {
                                                                                      Observation_match
                                                                                      [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                    }
                                                                                    ds
                                                                                  ]
                                                                                  [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]]
                                                                                }
                                                                                (lam
                                                                                  ds
                                                                                  [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                  (lam
                                                                                    ds
                                                                                    (con integer)
                                                                                    {
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
                                                                                            (all dead (type) [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]])
                                                                                          }
                                                                                          (abs
                                                                                            dead
                                                                                            (type)
                                                                                            (let
                                                                                              (nonrec
                                                                                              )
                                                                                              (termbind
                                                                                                (nonstrict
                                                                                                )
                                                                                                (vardecl
                                                                                                  r
                                                                                                  [[TxConstraints Void] Void]
                                                                                                )
                                                                                                [
                                                                                                  [
                                                                                                    {
                                                                                                      {
                                                                                                        fMonoidTxConstraints_c
                                                                                                        Void
                                                                                                      }
                                                                                                      Void
                                                                                                    }
                                                                                                    oracleConstraints
                                                                                                  ]
                                                                                                  [
                                                                                                    [
                                                                                                      payoutsTx
                                                                                                      [
                                                                                                        {
                                                                                                          [
                                                                                                            Margins_match
                                                                                                            accounts
                                                                                                          ]
                                                                                                          Payouts
                                                                                                        }
                                                                                                        (lam
                                                                                                          ds
                                                                                                          [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                          (lam
                                                                                                            ds
                                                                                                            [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                            (let
                                                                                                              (nonrec
                                                                                                              )
                                                                                                              (termbind
                                                                                                                (nonstrict
                                                                                                                )
                                                                                                                (vardecl
                                                                                                                  delta
                                                                                                                  [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                )
                                                                                                                [
                                                                                                                  [
                                                                                                                    fAdditiveGroupValue_cscale
                                                                                                                    ds
                                                                                                                  ]
                                                                                                                  [
                                                                                                                    [
                                                                                                                      fAdditiveGroupValue
                                                                                                                      ds
                                                                                                                    ]
                                                                                                                    ds
                                                                                                                  ]
                                                                                                                ]
                                                                                                              )
                                                                                                              [
                                                                                                                [
                                                                                                                  Payouts
                                                                                                                  [
                                                                                                                    [
                                                                                                                      fAdditiveGroupValue
                                                                                                                      ds
                                                                                                                    ]
                                                                                                                    delta
                                                                                                                  ]
                                                                                                                ]
                                                                                                                [
                                                                                                                  [
                                                                                                                    fAdditiveMonoidValue
                                                                                                                    ds
                                                                                                                  ]
                                                                                                                  delta
                                                                                                                ]
                                                                                                              ]
                                                                                                            )
                                                                                                          )
                                                                                                        )
                                                                                                      ]
                                                                                                    ]
                                                                                                    owners
                                                                                                  ]
                                                                                                ]
                                                                                              )
                                                                                              [
                                                                                                {
                                                                                                  Just
                                                                                                  [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]
                                                                                                }
                                                                                                [
                                                                                                  [
                                                                                                    {
                                                                                                      {
                                                                                                        Tuple2
                                                                                                        [[TxConstraints Void] Void]
                                                                                                      }
                                                                                                      [State FutureState]
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
                                                                                                                  [
                                                                                                                    {
                                                                                                                      {
                                                                                                                        TxConstraints_match
                                                                                                                        Void
                                                                                                                      }
                                                                                                                      Void
                                                                                                                    }
                                                                                                                    r
                                                                                                                  ]
                                                                                                                  [List TxConstraint]
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
                                                                                                                      ds
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
                                                                                                                            {
                                                                                                                              from
                                                                                                                              (con integer)
                                                                                                                            }
                                                                                                                            ds
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
                                                                                                                  r
                                                                                                                ]
                                                                                                                [List [InputConstraint Void]]
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
                                                                                                                    ds
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
                                                                                                                r
                                                                                                              ]
                                                                                                              [List [OutputConstraint Void]]
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
                                                                                                                  ds
                                                                                                                )
                                                                                                              )
                                                                                                            )
                                                                                                          ]
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
                                                                                                        FutureState
                                                                                                      }
                                                                                                      Finished
                                                                                                    ]
                                                                                                    {
                                                                                                      Nil
                                                                                                      [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                    }
                                                                                                  ]
                                                                                                ]
                                                                                              ]
                                                                                            )
                                                                                          )
                                                                                        ]
                                                                                        (abs
                                                                                          dead
                                                                                          (type)
                                                                                          {
                                                                                            Nothing
                                                                                            [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]
                                                                                          }
                                                                                        )
                                                                                      ]
                                                                                      (all dead (type) dead)
                                                                                    }
                                                                                  )
                                                                                )
                                                                              ]
                                                                            )
                                                                          )
                                                                        ]
                                                                      )
                                                                    ]
                                                                  )
                                                                ]
                                                                (lam
                                                                  ov
                                                                  [SignedMessage [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]]
                                                                  [
                                                                    [
                                                                      {
                                                                        [
                                                                          {
                                                                            {
                                                                              Either_match
                                                                              SignedMessageCheckError
                                                                            }
                                                                            [[Tuple2 [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]] [[TxConstraints Void] Void]]
                                                                          }
                                                                          [
                                                                            [
                                                                              [
                                                                                {
                                                                                  {
                                                                                    {
                                                                                      verifySignedMessageConstraints
                                                                                      [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                                                    }
                                                                                    Void
                                                                                  }
                                                                                  Void
                                                                                }
                                                                                futureStateMachine
                                                                              ]
                                                                              ds
                                                                            ]
                                                                            ov
                                                                          ]
                                                                        ]
                                                                        [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]]
                                                                      }
                                                                      (lam
                                                                        x
                                                                        SignedMessageCheckError
                                                                        {
                                                                          Nothing
                                                                          [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]
                                                                        }
                                                                      )
                                                                    ]
                                                                    (lam
                                                                      y
                                                                      [[Tuple2 [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]] [[TxConstraints Void] Void]]
                                                                      [
                                                                        {
                                                                          [
                                                                            {
                                                                              {
                                                                                Tuple2_match
                                                                                [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                                              }
                                                                              [[TxConstraints Void] Void]
                                                                            }
                                                                            y
                                                                          ]
                                                                          [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]]
                                                                        }
                                                                        (lam
                                                                          ds
                                                                          [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                                          (lam
                                                                            oracleConstraints
                                                                            [[TxConstraints Void] Void]
                                                                            [
                                                                              {
                                                                                [
                                                                                  {
                                                                                    Observation_match
                                                                                    [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                  }
                                                                                  ds
                                                                                ]
                                                                                [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]]
                                                                              }
                                                                              (lam
                                                                                ds
                                                                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                (lam
                                                                                  ds
                                                                                  (con integer)
                                                                                  {
                                                                                    [
                                                                                      [
                                                                                        {
                                                                                          [
                                                                                            {
                                                                                              Maybe_match
                                                                                              Role
                                                                                            }
                                                                                            [
                                                                                              [
                                                                                                [
                                                                                                  violatingRole
                                                                                                  future
                                                                                                ]
                                                                                                accounts
                                                                                              ]
                                                                                              ds
                                                                                            ]
                                                                                          ]
                                                                                          (all dead (type) [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]])
                                                                                        }
                                                                                        (lam
                                                                                          vRole
                                                                                          Role
                                                                                          (abs
                                                                                            dead
                                                                                            (type)
                                                                                            {
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
                                                                                                                  lessThanEqualsInteger
                                                                                                                )
                                                                                                                ds
                                                                                                              ]
                                                                                                              ds
                                                                                                            ]
                                                                                                          ]
                                                                                                          False
                                                                                                        ]
                                                                                                        True
                                                                                                      ]
                                                                                                    ]
                                                                                                    (all dead (type) [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]])
                                                                                                  }
                                                                                                  (abs
                                                                                                    dead
                                                                                                    (type)
                                                                                                    [
                                                                                                      {
                                                                                                        Just
                                                                                                        [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]
                                                                                                      }
                                                                                                      [
                                                                                                        [
                                                                                                          {
                                                                                                            {
                                                                                                              Tuple2
                                                                                                              [[TxConstraints Void] Void]
                                                                                                            }
                                                                                                            [State FutureState]
                                                                                                          }
                                                                                                          [
                                                                                                            [
                                                                                                              {
                                                                                                                {
                                                                                                                  fMonoidTxConstraints_c
                                                                                                                  Void
                                                                                                                }
                                                                                                                Void
                                                                                                              }
                                                                                                              {
                                                                                                                [
                                                                                                                  [
                                                                                                                    {
                                                                                                                      [
                                                                                                                        Role_match
                                                                                                                        vRole
                                                                                                                      ]
                                                                                                                      (all dead (type) [[TxConstraints Void] Void])
                                                                                                                    }
                                                                                                                    (abs
                                                                                                                      dead
                                                                                                                      (type)
                                                                                                                      [
                                                                                                                        [
                                                                                                                          [
                                                                                                                            {
                                                                                                                              {
                                                                                                                                mustPayToOtherScript
                                                                                                                                Void
                                                                                                                              }
                                                                                                                              Void
                                                                                                                            }
                                                                                                                            [
                                                                                                                              {
                                                                                                                                [
                                                                                                                                  FutureAccounts_match
                                                                                                                                  owners
                                                                                                                                ]
                                                                                                                                (con bytestring)
                                                                                                                              }
                                                                                                                              (lam
                                                                                                                                ds
                                                                                                                                [[Tuple2 (con bytestring)] (con bytestring)]
                                                                                                                                (lam
                                                                                                                                  ds
                                                                                                                                  (con bytestring)
                                                                                                                                  (lam
                                                                                                                                    ds
                                                                                                                                    [[Tuple2 (con bytestring)] (con bytestring)]
                                                                                                                                    (lam
                                                                                                                                      ds
                                                                                                                                      (con bytestring)
                                                                                                                                      ds
                                                                                                                                    )
                                                                                                                                  )
                                                                                                                                )
                                                                                                                              )
                                                                                                                            ]
                                                                                                                          ]
                                                                                                                          unitDatum
                                                                                                                        ]
                                                                                                                        [
                                                                                                                          {
                                                                                                                            [
                                                                                                                              Margins_match
                                                                                                                              accounts
                                                                                                                            ]
                                                                                                                            [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                          }
                                                                                                                          (lam
                                                                                                                            ds
                                                                                                                            [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                            (lam
                                                                                                                              ds
                                                                                                                              [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                              [
                                                                                                                                [
                                                                                                                                  fAdditiveMonoidValue
                                                                                                                                  ds
                                                                                                                                ]
                                                                                                                                ds
                                                                                                                              ]
                                                                                                                            )
                                                                                                                          )
                                                                                                                        ]
                                                                                                                      ]
                                                                                                                    )
                                                                                                                  ]
                                                                                                                  (abs
                                                                                                                    dead
                                                                                                                    (type)
                                                                                                                    [
                                                                                                                      [
                                                                                                                        [
                                                                                                                          {
                                                                                                                            {
                                                                                                                              mustPayToOtherScript
                                                                                                                              Void
                                                                                                                            }
                                                                                                                            Void
                                                                                                                          }
                                                                                                                          [
                                                                                                                            {
                                                                                                                              [
                                                                                                                                FutureAccounts_match
                                                                                                                                owners
                                                                                                                              ]
                                                                                                                              (con bytestring)
                                                                                                                            }
                                                                                                                            (lam
                                                                                                                              ds
                                                                                                                              [[Tuple2 (con bytestring)] (con bytestring)]
                                                                                                                              (lam
                                                                                                                                ds
                                                                                                                                (con bytestring)
                                                                                                                                (lam
                                                                                                                                  ds
                                                                                                                                  [[Tuple2 (con bytestring)] (con bytestring)]
                                                                                                                                  (lam
                                                                                                                                    ds
                                                                                                                                    (con bytestring)
                                                                                                                                    ds
                                                                                                                                  )
                                                                                                                                )
                                                                                                                              )
                                                                                                                            )
                                                                                                                          ]
                                                                                                                        ]
                                                                                                                        unitDatum
                                                                                                                      ]
                                                                                                                      [
                                                                                                                        {
                                                                                                                          [
                                                                                                                            Margins_match
                                                                                                                            accounts
                                                                                                                          ]
                                                                                                                          [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                        }
                                                                                                                        (lam
                                                                                                                          ds
                                                                                                                          [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                          (lam
                                                                                                                            ds
                                                                                                                            [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                            [
                                                                                                                              [
                                                                                                                                fAdditiveMonoidValue
                                                                                                                                ds
                                                                                                                              ]
                                                                                                                              ds
                                                                                                                            ]
                                                                                                                          )
                                                                                                                        )
                                                                                                                      ]
                                                                                                                    ]
                                                                                                                  )
                                                                                                                ]
                                                                                                                (all dead (type) dead)
                                                                                                              }
                                                                                                            ]
                                                                                                            oracleConstraints
                                                                                                          ]
                                                                                                        ]
                                                                                                        [
                                                                                                          [
                                                                                                            {
                                                                                                              State
                                                                                                              FutureState
                                                                                                            }
                                                                                                            Finished
                                                                                                          ]
                                                                                                          {
                                                                                                            Nil
                                                                                                            [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                          }
                                                                                                        ]
                                                                                                      ]
                                                                                                    ]
                                                                                                  )
                                                                                                ]
                                                                                                (abs
                                                                                                  dead
                                                                                                  (type)
                                                                                                  {
                                                                                                    Nothing
                                                                                                    [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]
                                                                                                  }
                                                                                                )
                                                                                              ]
                                                                                              (all dead (type) dead)
                                                                                            }
                                                                                          )
                                                                                        )
                                                                                      ]
                                                                                      (abs
                                                                                        dead
                                                                                        (type)
                                                                                        {
                                                                                          Nothing
                                                                                          [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]
                                                                                        }
                                                                                      )
                                                                                    ]
                                                                                    (all dead (type) dead)
                                                                                  }
                                                                                )
                                                                              )
                                                                            ]
                                                                          )
                                                                        )
                                                                      ]
                                                                    )
                                                                  ]
                                                                )
                                                              ]
                                                            )
                                                          )
                                                        ]
                                                        (all dead (type) dead)
                                                      }
                                                    )
                                                  )
                                                ]
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
                        )
                        (termbind
                          (strict)
                          (vardecl
                            futureStateMachine
                            (fun Future (fun FutureAccounts [[StateMachine FutureState] FutureAction]))
                          )
                          (lam
                            ft
                            Future
                            (lam
                              fos
                              FutureAccounts
                              [
                                [
                                  [
                                    [
                                      {
                                        { StateMachine FutureState }
                                        FutureAction
                                      }
                                      [ [ transition ft ] fos ]
                                    ]
                                    (lam
                                      ds
                                      FutureState
                                      {
                                        [
                                          [
                                            {
                                              [ FutureState_match ds ]
                                              (all dead (type) Bool)
                                            }
                                            (abs dead (type) True)
                                          ]
                                          (lam
                                            ipv Margins (abs dead (type) False)
                                          )
                                        ]
                                        (all dead (type) dead)
                                      }
                                    )
                                  ]
                                  {
                                    { mkStateMachine FutureState } FutureAction
                                  }
                                ]
                                { Nothing ThreadToken }
                              ]
                            )
                          )
                        )
                        futureStateMachine
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