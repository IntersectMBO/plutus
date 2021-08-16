(program
  (let
    (nonrec)
    (datatypebind
      (datatype
        (tyvardecl GameState (type))

        GameState_match
        (vardecl
          Initialised
          (fun (con bytestring) (fun (con bytestring) (fun (con bytestring) GameState)))
        )
        (vardecl
          Locked
          (fun (con bytestring) (fun (con bytestring) (fun (con bytestring) GameState)))
        )
      )
    )
    (termbind
      (strict)
      (vardecl fToDataGameState_ctoBuiltinData (fun GameState (con data)))
      (lam
        ds
        GameState
        [
          [
            { [ GameState_match ds ] (con data) }
            (lam
              arg
              (con bytestring)
              (lam
                arg
                (con bytestring)
                (lam
                  arg
                  (con bytestring)
                  [
                    [ (builtin constrData) (con integer 0) ]
                    [
                      [
                        { (builtin mkCons) (con data) } [ (builtin bData) arg ]
                      ]
                      [
                        [
                          { (builtin mkCons) (con data) }
                          [ (builtin bData) arg ]
                        ]
                        [
                          [
                            { (builtin mkCons) (con data) }
                            [ (builtin bData) arg ]
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
          (lam
            arg
            (con bytestring)
            (lam
              arg
              (con bytestring)
              (lam
                arg
                (con bytestring)
                [
                  [ (builtin constrData) (con integer 1) ]
                  [
                    [ { (builtin mkCons) (con data) } [ (builtin bData) arg ] ]
                    [
                      [
                        { (builtin mkCons) (con data) } [ (builtin bData) arg ]
                      ]
                      [
                        [
                          { (builtin mkCons) (con data) }
                          [ (builtin bData) arg ]
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
          DCertPoolRegister (fun (con bytestring) (fun (con bytestring) DCert))
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
        (vardecl TxOutRef (fun (con bytestring) (fun (con integer) TxOutRef)))
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
        (vardecl Interval (fun [LowerBound a] (fun [UpperBound a] [Interval a]))
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
            (datatypebind (datatype (tyvardecl Void (type))  Void_match ))
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
                        (datatypebind
                          (datatype
                            (tyvardecl Unit (type))

                            Unit_match
                            (vardecl Unit Unit)
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
                        (datatypebind
                          (datatype
                            (tyvardecl GameInput (type))

                            GameInput_match
                            (vardecl
                              Guess
                              (fun (con bytestring) (fun (con bytestring) (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] GameInput)))
                            )
                            (vardecl MintToken GameInput)
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
                            mkValidator
                            (fun (con bytestring) (fun (con bytestring) [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]))
                          )
                          (lam
                            mps
                            (con bytestring)
                            (lam
                              tn
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
                                      mps
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
                                            tn
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
                        (termbind
                          (strict)
                          (vardecl
                            transition
                            (fun [State GameState] (fun GameInput [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State GameState]]]))
                          )
                          (lam
                            ds
                            [State GameState]
                            (lam
                              input
                              GameInput
                              [
                                {
                                  [ { State_match GameState } ds ]
                                  [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State GameState]]]
                                }
                                (lam
                                  ds
                                  GameState
                                  (lam
                                    ds
                                    [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                    [
                                      [
                                        {
                                          [ GameState_match ds ]
                                          [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State GameState]]]
                                        }
                                        (lam
                                          mph
                                          (con bytestring)
                                          (lam
                                            tn
                                            (con bytestring)
                                            (lam
                                              s
                                              (con bytestring)
                                              {
                                                [
                                                  [
                                                    {
                                                      [ GameInput_match input ]
                                                      (all dead (type) [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State GameState]]])
                                                    }
                                                    (lam
                                                      ipv
                                                      (con bytestring)
                                                      (lam
                                                        ipv
                                                        (con bytestring)
                                                        (lam
                                                          ipv
                                                          [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                          (abs
                                                            dead
                                                            (type)
                                                            {
                                                              Nothing
                                                              [[Tuple2 [[TxConstraints Void] Void]] [State GameState]]
                                                            }
                                                          )
                                                        )
                                                      )
                                                    )
                                                  ]
                                                  (abs
                                                    dead
                                                    (type)
                                                    [
                                                      {
                                                        Just
                                                        [[Tuple2 [[TxConstraints Void] Void]] [State GameState]]
                                                      }
                                                      [
                                                        [
                                                          {
                                                            {
                                                              Tuple2
                                                              [[TxConstraints Void] Void]
                                                            }
                                                            [State GameState]
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
                                                                              [
                                                                                [
                                                                                  [
                                                                                    MustMintValue
                                                                                    mph
                                                                                  ]
                                                                                  [
                                                                                    fToDataUnit_ctoBuiltinData
                                                                                    Unit
                                                                                  ]
                                                                                ]
                                                                                tn
                                                                              ]
                                                                              (con
                                                                                integer
                                                                                  1
                                                                              )
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
                                                            { State GameState }
                                                            [
                                                              [
                                                                [ Locked mph ]
                                                                tn
                                                              ]
                                                              s
                                                            ]
                                                          ]
                                                          ds
                                                        ]
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
                                      (lam
                                        mph
                                        (con bytestring)
                                        (lam
                                          tn
                                          (con bytestring)
                                          (lam
                                            currentSecret
                                            (con bytestring)
                                            {
                                              [
                                                [
                                                  {
                                                    [ GameInput_match input ]
                                                    (all dead (type) [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State GameState]]])
                                                  }
                                                  (lam
                                                    theGuess
                                                    (con bytestring)
                                                    (lam
                                                      nextSecret
                                                      (con bytestring)
                                                      (lam
                                                        takenOut
                                                        [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
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
                                                                                equalsByteString
                                                                              )
                                                                              currentSecret
                                                                            ]
                                                                            [
                                                                              (builtin
                                                                                sha2_256
                                                                              )
                                                                              theGuess
                                                                            ]
                                                                          ]
                                                                        ]
                                                                        True
                                                                      ]
                                                                      False
                                                                    ]
                                                                  ]
                                                                  (all dead (type) [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State GameState]]])
                                                                }
                                                                (abs
                                                                  dead
                                                                  (type)
                                                                  [
                                                                    {
                                                                      Just
                                                                      [[Tuple2 [[TxConstraints Void] Void]] [State GameState]]
                                                                    }
                                                                    [
                                                                      [
                                                                        {
                                                                          {
                                                                            Tuple2
                                                                            [[TxConstraints Void] Void]
                                                                          }
                                                                          [State GameState]
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
                                                                                                  [
                                                                                                    [
                                                                                                      MustMintValue
                                                                                                      mph
                                                                                                    ]
                                                                                                    [
                                                                                                      fToDataUnit_ctoBuiltinData
                                                                                                      Unit
                                                                                                    ]
                                                                                                  ]
                                                                                                  tn
                                                                                                ]
                                                                                                (con
                                                                                                  integer
                                                                                                    0
                                                                                                )
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
                                                                                              MustSpendAtLeast
                                                                                              [
                                                                                                [
                                                                                                  mkValidator
                                                                                                  mph
                                                                                                ]
                                                                                                tn
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
                                                                            GameState
                                                                          }
                                                                          [
                                                                            [
                                                                              [
                                                                                Locked
                                                                                mph
                                                                              ]
                                                                              tn
                                                                            ]
                                                                            nextSecret
                                                                          ]
                                                                        ]
                                                                        [
                                                                          [
                                                                            fAdditiveGroupValue
                                                                            ds
                                                                          ]
                                                                          takenOut
                                                                        ]
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
                                                                  [[Tuple2 [[TxConstraints Void] Void]] [State GameState]]
                                                                }
                                                              )
                                                            ]
                                                            (all dead (type) dead)
                                                          }
                                                        )
                                                      )
                                                    )
                                                  )
                                                ]
                                                (abs
                                                  dead
                                                  (type)
                                                  {
                                                    Nothing
                                                    [[Tuple2 [[TxConstraints Void] Void]] [State GameState]]
                                                  }
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
                              ]
                            )
                          )
                        )
                        (termbind
                          (nonstrict)
                          (vardecl machine [[StateMachine GameState] GameInput])
                          [
                            [
                              [
                                [
                                  { { StateMachine GameState } GameInput }
                                  transition
                                ]
                                (lam ds GameState False)
                              ]
                              { { mkStateMachine GameState } GameInput }
                            ]
                            { Nothing ThreadToken }
                          ]
                        )
                        (termbind
                          (strict)
                          (vardecl absurd (all a (type) (fun Void a)))
                          (abs a (type) (lam a Void { [ Void_match a ] a }))
                        )
                        (termbind
                          (strict)
                          (vardecl
                            fToDataVoid_ctoBuiltinData (fun Void (con data))
                          )
                          (lam v Void [ { absurd (con data) } v ])
                        )
                        (termbind
                          (strict)
                          (vardecl
                            fEqTxOutRef_c (fun TxOutRef (fun TxOutRef Bool))
                          )
                          (lam
                            l
                            TxOutRef
                            (lam
                              r
                              TxOutRef
                              {
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
                                      (all dead (type) Bool)
                                    }
                                    (abs
                                      dead
                                      (type)
                                      [
                                        [
                                          [
                                            { (builtin ifThenElse) Bool }
                                            [
                                              [
                                                (builtin equalsInteger)
                                                [
                                                  {
                                                    [ TxOutRef_match l ]
                                                    (con integer)
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
                                                  (con integer)
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
                                    )
                                  ]
                                  (abs dead (type) False)
                                ]
                                (all dead (type) dead)
                              }
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
                                        {
                                          [ { InputConstraint_match a } ds ]
                                          Bool
                                        }
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
                                                                          (all dead (type) Bool)
                                                                        }
                                                                        (abs
                                                                          dead
                                                                          (type)
                                                                          True
                                                                        )
                                                                      ]
                                                                      (abs
                                                                        dead
                                                                        (type)
                                                                        [
                                                                          [
                                                                            {
                                                                              (builtin
                                                                                trace
                                                                              )
                                                                              Bool
                                                                            }
                                                                            (con
                                                                              string
                                                                                "L0"
                                                                            )
                                                                          ]
                                                                          False
                                                                        ]
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
                                {
                                  [
                                    [
                                      {
                                        [ { Maybe_match a } ds ]
                                        (all dead (type) [(lam a (type) [Maybe a]) a])
                                      }
                                      (lam ipv a (abs dead (type) ds))
                                    ]
                                    (abs dead (type) b)
                                  ]
                                  (all dead (type) dead)
                                }
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
                                                    {
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
                                                                                  (all dead (type) [Maybe [[Tuple2 (con bytestring)] (con data)]])
                                                                                }
                                                                                (abs
                                                                                  dead
                                                                                  (type)
                                                                                  [
                                                                                    {
                                                                                      Just
                                                                                      [[Tuple2 (con bytestring)] (con data)]
                                                                                    }
                                                                                    x
                                                                                  ]
                                                                                )
                                                                              ]
                                                                              (abs
                                                                                dead
                                                                                (type)
                                                                                {
                                                                                  Nothing
                                                                                  [[Tuple2 (con bytestring)] (con data)]
                                                                                }
                                                                              )
                                                                            ]
                                                                            (all dead (type) dead)
                                                                          }
                                                                        )
                                                                      )
                                                                    ]
                                                                  )
                                                                ]
                                                                ds
                                                              ]
                                                            ]
                                                            (all dead (type) [Maybe (con bytestring)])
                                                          }
                                                          (lam
                                                            a
                                                            [[Tuple2 (con bytestring)] (con data)]
                                                            (abs
                                                              dead
                                                              (type)
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
                                                                      ds
                                                                      (con data)
                                                                      a
                                                                    )
                                                                  )
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
                                                            (con bytestring)
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
                            fEqCredential_c
                            (fun Credential (fun Credential Bool))
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
                                      a
                                      (con bytestring)
                                      [ [ equalsByteString a ] a ]
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
                            equalsInteger
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
                                        (lam
                                          r
                                          Credential
                                          [ [ fEqCredential_c l ] r ]
                                        )
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
                                          {
                                            [ StakingCredential_match ds ] Bool
                                          }
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
                                                      (all dead (type) Bool)
                                                    }
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
                                                              (all dead (type) Bool)
                                                            }
                                                            (abs
                                                              dead
                                                              (type)
                                                              [
                                                                [
                                                                  equalsInteger
                                                                  c
                                                                ]
                                                                c
                                                              ]
                                                            )
                                                          ]
                                                          (abs dead (type) False
                                                          )
                                                        ]
                                                        (all dead (type) dead)
                                                      }
                                                    )
                                                  ]
                                                  (abs dead (type) False)
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
                              ]
                            )
                          )
                        )
                        (termbind
                          (strict)
                          (vardecl fEqAddress_c (fun Address (fun Address Bool))
                          )
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
                                              {
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
                                                      (all dead (type) Bool)
                                                    }
                                                    (lam
                                                      a
                                                      StakingCredential
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
                                                                    StakingCredential
                                                                  }
                                                                  stakingCred
                                                                ]
                                                                (all dead (type) Bool)
                                                              }
                                                              (lam
                                                                a
                                                                StakingCredential
                                                                (abs
                                                                  dead
                                                                  (type)
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
                                                            (abs
                                                              dead (type) False
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
                                                            (all dead (type) Bool)
                                                          }
                                                          (lam
                                                            ipv
                                                            StakingCredential
                                                            (abs
                                                              dead (type) False
                                                            )
                                                          )
                                                        ]
                                                        (abs dead (type) True)
                                                      ]
                                                      (all dead (type) dead)
                                                    }
                                                  )
                                                ]
                                                (all dead (type) dead)
                                              }
                                            )
                                            [
                                              [
                                                {
                                                  [ Credential_match cred ] Bool
                                                }
                                                (lam
                                                  l
                                                  (con bytestring)
                                                  [
                                                    [
                                                      {
                                                        [
                                                          Credential_match cred
                                                        ]
                                                        Bool
                                                      }
                                                      (lam
                                                        r
                                                        (con bytestring)
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
                                                                (all dead (type) Bool)
                                                              }
                                                              (abs dead (type) j
                                                              )
                                                            ]
                                                            (abs
                                                              dead (type) False
                                                            )
                                                          ]
                                                          (all dead (type) dead)
                                                        }
                                                      )
                                                    ]
                                                    (lam
                                                      ipv (con bytestring) False
                                                    )
                                                  ]
                                                )
                                              ]
                                              (lam
                                                a
                                                (con bytestring)
                                                [
                                                  [
                                                    {
                                                      [ Credential_match cred ]
                                                      Bool
                                                    }
                                                    (lam
                                                      ipv (con bytestring) False
                                                    )
                                                  ]
                                                  (lam
                                                    a
                                                    (con bytestring)
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
                                                            (all dead (type) Bool)
                                                          }
                                                          (abs dead (type) j)
                                                        ]
                                                        (abs dead (type) False)
                                                      ]
                                                      (all dead (type) dead)
                                                    }
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
                          (vardecl
                            findOwnInput (fun ScriptContext [Maybe TxInInfo])
                          )
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
                                                        {
                                                          [
                                                            [
                                                              [
                                                                [
                                                                  {
                                                                    [
                                                                      ScriptPurpose_match
                                                                      ds
                                                                    ]
                                                                    (all dead (type) [Maybe TxInInfo])
                                                                  }
                                                                  (lam
                                                                    default_arg0
                                                                    DCert
                                                                    (abs
                                                                      dead
                                                                      (type)
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
                                                                  (abs
                                                                    dead
                                                                    (type)
                                                                    {
                                                                      Nothing
                                                                      TxInInfo
                                                                    }
                                                                  )
                                                                )
                                                              ]
                                                              (lam
                                                                default_arg0
                                                                StakingCredential
                                                                (abs
                                                                  dead
                                                                  (type)
                                                                  {
                                                                    Nothing
                                                                    TxInInfo
                                                                  }
                                                                )
                                                              )
                                                            ]
                                                            (lam
                                                              txOutRef
                                                              TxOutRef
                                                              (abs
                                                                dead
                                                                (type)
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
                                                                            {
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
                                                                                    (all dead (type) [Maybe TxInInfo])
                                                                                  }
                                                                                  (abs
                                                                                    dead
                                                                                    (type)
                                                                                    [
                                                                                      {
                                                                                        Just
                                                                                        TxInInfo
                                                                                      }
                                                                                      x
                                                                                    ]
                                                                                  )
                                                                                ]
                                                                                (abs
                                                                                  dead
                                                                                  (type)
                                                                                  {
                                                                                    Nothing
                                                                                    TxInInfo
                                                                                  }
                                                                                )
                                                                              ]
                                                                              (all dead (type) dead)
                                                                            }
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
                                                          (all dead (type) dead)
                                                        }
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
                        (termbind
                          (strict)
                          (vardecl
                            getContinuingOutputs
                            (fun ScriptContext [List TxOut])
                          )
                          (lam
                            ctx
                            ScriptContext
                            {
                              [
                                [
                                  {
                                    [
                                      { Maybe_match TxInInfo }
                                      [ findOwnInput ctx ]
                                    ]
                                    (all dead (type) [List TxOut])
                                  }
                                  (lam
                                    ds
                                    TxInInfo
                                    (abs
                                      dead
                                      (type)
                                      [
                                        { [ TxInInfo_match ds ] [List TxOut] }
                                        (lam
                                          ds
                                          TxOutRef
                                          (lam
                                            ds
                                            TxOut
                                            [
                                              {
                                                [ TxOut_match ds ] [List TxOut]
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
                                                          ScriptContext_match
                                                          ctx
                                                        ]
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
                                                              [
                                                                TxInfo_match ds
                                                              ]
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
                                                                                                  {
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
                                                                                                          (all dead (type) [List TxOut])
                                                                                                        }
                                                                                                        (abs
                                                                                                          dead
                                                                                                          (type)
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
                                                                                                      (abs
                                                                                                        dead
                                                                                                        (type)
                                                                                                        xs
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
                                (abs
                                  dead
                                  (type)
                                  [
                                    { error [List TxOut] }
                                    [
                                      {
                                        [
                                          Unit_match
                                          [
                                            [
                                              { (builtin trace) Unit }
                                              (con string "Lf")
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
                              (all dead (type) dead)
                            }
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
                                          {
                                            [ { OutputConstraint_match o } ds ]
                                            Bool
                                          }
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
                                                    [
                                                      findDatumHash
                                                      [ dToData ds ]
                                                    ]
                                                    ds
                                                  ]
                                                )
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
                                                                        {
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
                                                                                (all dead (type) Bool)
                                                                              }
                                                                              (lam
                                                                                svh
                                                                                (con bytestring)
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
                                                                                                  checkBinRel
                                                                                                  equalsInteger
                                                                                                ]
                                                                                                ds
                                                                                              ]
                                                                                              ds
                                                                                            ]
                                                                                          ]
                                                                                          (all dead (type) Bool)
                                                                                        }
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
                                                                                                      (con bytestring)
                                                                                                    }
                                                                                                    hsh
                                                                                                  ]
                                                                                                  (all dead (type) Bool)
                                                                                                }
                                                                                                (lam
                                                                                                  a
                                                                                                  (con bytestring)
                                                                                                  (abs
                                                                                                    dead
                                                                                                    (type)
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
                                                                                              (abs
                                                                                                dead
                                                                                                (type)
                                                                                                False
                                                                                              )
                                                                                            ]
                                                                                            (all dead (type) dead)
                                                                                          }
                                                                                        )
                                                                                      ]
                                                                                      (abs
                                                                                        dead
                                                                                        (type)
                                                                                        False
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
                                                                              False
                                                                            )
                                                                          ]
                                                                          (all dead (type) dead)
                                                                        }
                                                                      )
                                                                    )
                                                                  )
                                                                ]
                                                              )
                                                            ]
                                                            [
                                                              getContinuingOutputs
                                                              ctx
                                                            ]
                                                          ]
                                                        ]
                                                        (all dead (type) Bool)
                                                      }
                                                      (abs dead (type) True)
                                                    ]
                                                    (abs
                                                      dead
                                                      (type)
                                                      [
                                                        [
                                                          {
                                                            (builtin trace) Bool
                                                          }
                                                          (con string "L1")
                                                        ]
                                                        False
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
                            fOrdInteger_ccompare
                            (fun (con integer) (fun (con integer) Ordering))
                          )
                          (lam
                            x
                            (con integer)
                            (lam
                              y
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
                                              { (builtin ifThenElse) Bool }
                                              [
                                                [ (builtin equalsInteger) x ] y
                                              ]
                                            ]
                                            True
                                          ]
                                          False
                                        ]
                                      ]
                                      (all dead (type) Ordering)
                                    }
                                    (abs dead (type) EQ)
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
                                                  [
                                                    {
                                                      (builtin ifThenElse) Bool
                                                    }
                                                    [
                                                      [
                                                        (builtin
                                                          lessThanEqualsInteger
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
                                            (all dead (type) Ordering)
                                          }
                                          (abs dead (type) LT)
                                        ]
                                        (abs dead (type) GT)
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
                              {
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
                                      (all dead (type) (con integer))
                                    }
                                    (abs dead (type) y)
                                  ]
                                  (abs dead (type) x)
                                ]
                                (all dead (type) dead)
                              }
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
                              {
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
                                      (all dead (type) (con integer))
                                    }
                                    (abs dead (type) x)
                                  ]
                                  (abs dead (type) y)
                                ]
                                (all dead (type) dead)
                              }
                            )
                          )
                        )
                        (termbind
                          (strict)
                          (vardecl
                            greaterThanEqualsInteger
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
                                  False
                                ]
                                True
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
                                    [ [ (builtin lessThanEqualsInteger) x ] y ]
                                  ]
                                  False
                                ]
                                True
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
                          (strict)
                          (vardecl
                            lessThanEqualsInteger
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
                          (nonstrict)
                          (vardecl fOrdPOSIXTime [Ord (con integer)])
                          [
                            [
                              [
                                [
                                  [
                                    [
                                      [
                                        [
                                          { CConsOrd (con integer) }
                                          equalsInteger
                                        ]
                                        fOrdInteger_ccompare
                                      ]
                                      lessThanInteger
                                    ]
                                    lessThanEqualsInteger
                                  ]
                                  greaterThanInteger
                                ]
                                greaterThanEqualsInteger
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
                                {
                                  [ { Ord_match a } v ] (fun a (fun a Ordering))
                                }
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
                                      (vardecl
                                        fail (fun (all a (type) a) Ordering)
                                      )
                                      (lam ds (all a (type) a) (error Ordering))
                                    )
                                    {
                                      [
                                        [
                                          [
                                            {
                                              [ { Extended_match a } ds ]
                                              (all dead (type) Ordering)
                                            }
                                            (lam
                                              default_arg0
                                              a
                                              (abs
                                                dead
                                                (type)
                                                {
                                                  [
                                                    [
                                                      [
                                                        {
                                                          [
                                                            { Extended_match a }
                                                            ds
                                                          ]
                                                          (all dead (type) Ordering)
                                                        }
                                                        (lam
                                                          default_arg0
                                                          a
                                                          (abs
                                                            dead
                                                            (type)
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
                                                                  {
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
                                                                            (all dead (type) Ordering)
                                                                          }
                                                                          (lam
                                                                            default_arg0
                                                                            a
                                                                            (abs
                                                                              dead
                                                                              (type)
                                                                              {
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
                                                                                        (all dead (type) Ordering)
                                                                                      }
                                                                                      (lam
                                                                                        l
                                                                                        a
                                                                                        (abs
                                                                                          dead
                                                                                          (type)
                                                                                          {
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
                                                                                                    (all dead (type) Ordering)
                                                                                                  }
                                                                                                  (lam
                                                                                                    r
                                                                                                    a
                                                                                                    (abs
                                                                                                      dead
                                                                                                      (type)
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
                                                                                                (abs
                                                                                                  dead
                                                                                                  (type)
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
                                                                                              (abs
                                                                                                dead
                                                                                                (type)
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
                                                                                            (all dead (type) dead)
                                                                                          }
                                                                                        )
                                                                                      )
                                                                                    ]
                                                                                    (abs
                                                                                      dead
                                                                                      (type)
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
                                                                                  (abs
                                                                                    dead
                                                                                    (type)
                                                                                    GT
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
                                                                                    (all dead (type) Ordering)
                                                                                  }
                                                                                  (lam
                                                                                    l
                                                                                    a
                                                                                    (abs
                                                                                      dead
                                                                                      (type)
                                                                                      {
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
                                                                                                (all dead (type) Ordering)
                                                                                              }
                                                                                              (lam
                                                                                                r
                                                                                                a
                                                                                                (abs
                                                                                                  dead
                                                                                                  (type)
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
                                                                                            (abs
                                                                                              dead
                                                                                              (type)
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
                                                                                          (abs
                                                                                            dead
                                                                                            (type)
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
                                                                                        (all dead (type) dead)
                                                                                      }
                                                                                    )
                                                                                  )
                                                                                ]
                                                                                (abs
                                                                                  dead
                                                                                  (type)
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
                                                                              (abs
                                                                                dead
                                                                                (type)
                                                                                GT
                                                                              )
                                                                            ]
                                                                            (all dead (type) dead)
                                                                          }
                                                                        )
                                                                      ]
                                                                      (abs
                                                                        dead
                                                                        (type)
                                                                        LT
                                                                      )
                                                                    ]
                                                                    (all dead (type) dead)
                                                                  }
                                                                )
                                                              )
                                                              {
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
                                                                        (all dead (type) Ordering)
                                                                      }
                                                                      (lam
                                                                        default_arg0
                                                                        a
                                                                        (abs
                                                                          dead
                                                                          (type)
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
                                                                    (abs
                                                                      dead
                                                                      (type)
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
                                                                  (abs
                                                                    dead
                                                                    (type)
                                                                    {
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
                                                                              (all dead (type) Ordering)
                                                                            }
                                                                            (lam
                                                                              default_arg0
                                                                              a
                                                                              (abs
                                                                                dead
                                                                                (type)
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
                                                                          (abs
                                                                            dead
                                                                            (type)
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
                                                                        (abs
                                                                          dead
                                                                          (type)
                                                                          EQ
                                                                        )
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
                                                      ]
                                                      (abs dead (type) GT)
                                                    ]
                                                    (abs
                                                      dead
                                                      (type)
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
                                                            {
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
                                                                      (all dead (type) Ordering)
                                                                    }
                                                                    (lam
                                                                      default_arg0
                                                                      a
                                                                      (abs
                                                                        dead
                                                                        (type)
                                                                        {
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
                                                                                  (all dead (type) Ordering)
                                                                                }
                                                                                (lam
                                                                                  l
                                                                                  a
                                                                                  (abs
                                                                                    dead
                                                                                    (type)
                                                                                    {
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
                                                                                              (all dead (type) Ordering)
                                                                                            }
                                                                                            (lam
                                                                                              r
                                                                                              a
                                                                                              (abs
                                                                                                dead
                                                                                                (type)
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
                                                                                          (abs
                                                                                            dead
                                                                                            (type)
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
                                                                                        (abs
                                                                                          dead
                                                                                          (type)
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
                                                                                      (all dead (type) dead)
                                                                                    }
                                                                                  )
                                                                                )
                                                                              ]
                                                                              (abs
                                                                                dead
                                                                                (type)
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
                                                                            (abs
                                                                              dead
                                                                              (type)
                                                                              GT
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
                                                                              (all dead (type) Ordering)
                                                                            }
                                                                            (lam
                                                                              l
                                                                              a
                                                                              (abs
                                                                                dead
                                                                                (type)
                                                                                {
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
                                                                                          (all dead (type) Ordering)
                                                                                        }
                                                                                        (lam
                                                                                          r
                                                                                          a
                                                                                          (abs
                                                                                            dead
                                                                                            (type)
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
                                                                                      (abs
                                                                                        dead
                                                                                        (type)
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
                                                                                    (abs
                                                                                      dead
                                                                                      (type)
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
                                                                                  (all dead (type) dead)
                                                                                }
                                                                              )
                                                                            )
                                                                          ]
                                                                          (abs
                                                                            dead
                                                                            (type)
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
                                                                        (abs
                                                                          dead
                                                                          (type)
                                                                          GT
                                                                        )
                                                                      ]
                                                                      (all dead (type) dead)
                                                                    }
                                                                  )
                                                                ]
                                                                (abs
                                                                  dead (type) LT
                                                                )
                                                              ]
                                                              (all dead (type) dead)
                                                            }
                                                          )
                                                        )
                                                        {
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
                                                                  (all dead (type) Ordering)
                                                                }
                                                                (lam
                                                                  default_arg0
                                                                  a
                                                                  (abs
                                                                    dead
                                                                    (type)
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
                                                              (abs
                                                                dead
                                                                (type)
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
                                                            (abs
                                                              dead
                                                              (type)
                                                              {
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
                                                                        (all dead (type) Ordering)
                                                                      }
                                                                      (lam
                                                                        default_arg0
                                                                        a
                                                                        (abs
                                                                          dead
                                                                          (type)
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
                                                                    (abs
                                                                      dead
                                                                      (type)
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
                                                                  (abs
                                                                    dead
                                                                    (type)
                                                                    EQ
                                                                  )
                                                                ]
                                                                (all dead (type) dead)
                                                              }
                                                            )
                                                          ]
                                                          (all dead (type) dead)
                                                        }
                                                      )
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
                                              [
                                                [
                                                  [
                                                    {
                                                      [
                                                        { Extended_match a } ds
                                                      ]
                                                      (all dead (type) Ordering)
                                                    }
                                                    (lam
                                                      default_arg0
                                                      a
                                                      (abs dead (type) LT)
                                                    )
                                                  ]
                                                  (abs dead (type) EQ)
                                                ]
                                                (abs dead (type) LT)
                                              ]
                                              (all dead (type) dead)
                                            }
                                          )
                                        ]
                                        (abs
                                          dead
                                          (type)
                                          {
                                            [
                                              [
                                                [
                                                  {
                                                    [ { Extended_match a } ds ]
                                                    (all dead (type) Ordering)
                                                  }
                                                  (lam
                                                    default_arg0
                                                    a
                                                    (abs
                                                      dead
                                                      (type)
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
                                                            {
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
                                                                      (all dead (type) Ordering)
                                                                    }
                                                                    (lam
                                                                      default_arg0
                                                                      a
                                                                      (abs
                                                                        dead
                                                                        (type)
                                                                        {
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
                                                                                  (all dead (type) Ordering)
                                                                                }
                                                                                (lam
                                                                                  l
                                                                                  a
                                                                                  (abs
                                                                                    dead
                                                                                    (type)
                                                                                    {
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
                                                                                              (all dead (type) Ordering)
                                                                                            }
                                                                                            (lam
                                                                                              r
                                                                                              a
                                                                                              (abs
                                                                                                dead
                                                                                                (type)
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
                                                                                          (abs
                                                                                            dead
                                                                                            (type)
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
                                                                                        (abs
                                                                                          dead
                                                                                          (type)
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
                                                                                      (all dead (type) dead)
                                                                                    }
                                                                                  )
                                                                                )
                                                                              ]
                                                                              (abs
                                                                                dead
                                                                                (type)
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
                                                                            (abs
                                                                              dead
                                                                              (type)
                                                                              GT
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
                                                                              (all dead (type) Ordering)
                                                                            }
                                                                            (lam
                                                                              l
                                                                              a
                                                                              (abs
                                                                                dead
                                                                                (type)
                                                                                {
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
                                                                                          (all dead (type) Ordering)
                                                                                        }
                                                                                        (lam
                                                                                          r
                                                                                          a
                                                                                          (abs
                                                                                            dead
                                                                                            (type)
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
                                                                                      (abs
                                                                                        dead
                                                                                        (type)
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
                                                                                    (abs
                                                                                      dead
                                                                                      (type)
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
                                                                                  (all dead (type) dead)
                                                                                }
                                                                              )
                                                                            )
                                                                          ]
                                                                          (abs
                                                                            dead
                                                                            (type)
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
                                                                        (abs
                                                                          dead
                                                                          (type)
                                                                          GT
                                                                        )
                                                                      ]
                                                                      (all dead (type) dead)
                                                                    }
                                                                  )
                                                                ]
                                                                (abs
                                                                  dead (type) LT
                                                                )
                                                              ]
                                                              (all dead (type) dead)
                                                            }
                                                          )
                                                        )
                                                        {
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
                                                                  (all dead (type) Ordering)
                                                                }
                                                                (lam
                                                                  default_arg0
                                                                  a
                                                                  (abs
                                                                    dead
                                                                    (type)
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
                                                              (abs
                                                                dead
                                                                (type)
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
                                                            (abs
                                                              dead
                                                              (type)
                                                              {
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
                                                                        (all dead (type) Ordering)
                                                                      }
                                                                      (lam
                                                                        default_arg0
                                                                        a
                                                                        (abs
                                                                          dead
                                                                          (type)
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
                                                                    (abs
                                                                      dead
                                                                      (type)
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
                                                                  (abs
                                                                    dead
                                                                    (type)
                                                                    EQ
                                                                  )
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
                                                ]
                                                (abs dead (type) GT)
                                              ]
                                              (abs
                                                dead
                                                (type)
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
                                                      {
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
                                                                (all dead (type) Ordering)
                                                              }
                                                              (lam
                                                                default_arg0
                                                                a
                                                                (abs
                                                                  dead
                                                                  (type)
                                                                  {
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
                                                                            (all dead (type) Ordering)
                                                                          }
                                                                          (lam
                                                                            l
                                                                            a
                                                                            (abs
                                                                              dead
                                                                              (type)
                                                                              {
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
                                                                                        (all dead (type) Ordering)
                                                                                      }
                                                                                      (lam
                                                                                        r
                                                                                        a
                                                                                        (abs
                                                                                          dead
                                                                                          (type)
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
                                                                                    (abs
                                                                                      dead
                                                                                      (type)
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
                                                                                  (abs
                                                                                    dead
                                                                                    (type)
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
                                                                                (all dead (type) dead)
                                                                              }
                                                                            )
                                                                          )
                                                                        ]
                                                                        (abs
                                                                          dead
                                                                          (type)
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
                                                                      (abs
                                                                        dead
                                                                        (type)
                                                                        GT
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
                                                                        (all dead (type) Ordering)
                                                                      }
                                                                      (lam
                                                                        l
                                                                        a
                                                                        (abs
                                                                          dead
                                                                          (type)
                                                                          {
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
                                                                                    (all dead (type) Ordering)
                                                                                  }
                                                                                  (lam
                                                                                    r
                                                                                    a
                                                                                    (abs
                                                                                      dead
                                                                                      (type)
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
                                                                                (abs
                                                                                  dead
                                                                                  (type)
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
                                                                              (abs
                                                                                dead
                                                                                (type)
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
                                                                            (all dead (type) dead)
                                                                          }
                                                                        )
                                                                      )
                                                                    ]
                                                                    (abs
                                                                      dead
                                                                      (type)
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
                                                                  (abs
                                                                    dead
                                                                    (type)
                                                                    GT
                                                                  )
                                                                ]
                                                                (all dead (type) dead)
                                                              }
                                                            )
                                                          ]
                                                          (abs dead (type) LT)
                                                        ]
                                                        (all dead (type) dead)
                                                      }
                                                    )
                                                  )
                                                  {
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
                                                            (all dead (type) Ordering)
                                                          }
                                                          (lam
                                                            default_arg0
                                                            a
                                                            (abs
                                                              dead
                                                              (type)
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
                                                        (abs
                                                          dead
                                                          (type)
                                                          [
                                                            fail
                                                            (abs
                                                              e (type) (error e)
                                                            )
                                                          ]
                                                        )
                                                      ]
                                                      (abs
                                                        dead
                                                        (type)
                                                        {
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
                                                                  (all dead (type) Ordering)
                                                                }
                                                                (lam
                                                                  default_arg0
                                                                  a
                                                                  (abs
                                                                    dead
                                                                    (type)
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
                                                              (abs
                                                                dead
                                                                (type)
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
                                                            (abs dead (type) EQ)
                                                          ]
                                                          (all dead (type) dead)
                                                        }
                                                      )
                                                    ]
                                                    (all dead (type) dead)
                                                  }
                                                )
                                              )
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
                                              {
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
                                                        (all dead (type) Bool)
                                                      }
                                                      (abs
                                                        dead
                                                        (type)
                                                        {
                                                          [
                                                            [
                                                              {
                                                                [
                                                                  Bool_match in
                                                                ]
                                                                (all dead (type) Bool)
                                                              }
                                                              (abs
                                                                dead (type) in
                                                              )
                                                            ]
                                                            (abs
                                                              dead (type) True
                                                            )
                                                          ]
                                                          (all dead (type) dead)
                                                        }
                                                      )
                                                    ]
                                                    (abs dead (type) False)
                                                  ]
                                                  (abs dead (type) True)
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
                                                    [
                                                      {
                                                        [
                                                          { LowerBound_match a }
                                                          l
                                                        ]
                                                        Bool
                                                      }
                                                      (lam
                                                        v
                                                        [Extended a]
                                                        (lam
                                                          in
                                                          Bool
                                                          {
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
                                                                    (all dead (type) Bool)
                                                                  }
                                                                  (abs
                                                                    dead
                                                                    (type)
                                                                    {
                                                                      [
                                                                        [
                                                                          {
                                                                            [
                                                                              Bool_match
                                                                              in
                                                                            ]
                                                                            (all dead (type) Bool)
                                                                          }
                                                                          (abs
                                                                            dead
                                                                            (type)
                                                                            {
                                                                              [
                                                                                [
                                                                                  {
                                                                                    [
                                                                                      Bool_match
                                                                                      in
                                                                                    ]
                                                                                    (all dead (type) Bool)
                                                                                  }
                                                                                  (abs
                                                                                    dead
                                                                                    (type)
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
                                                                                (abs
                                                                                  dead
                                                                                  (type)
                                                                                  False
                                                                                )
                                                                              ]
                                                                              (all dead (type) dead)
                                                                            }
                                                                          )
                                                                        ]
                                                                        (abs
                                                                          dead
                                                                          (type)
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
                                                                      (all dead (type) dead)
                                                                    }
                                                                  )
                                                                ]
                                                                (abs
                                                                  dead
                                                                  (type)
                                                                  False
                                                                )
                                                              ]
                                                              (abs
                                                                dead
                                                                (type)
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
                                                            (all dead (type) dead)
                                                          }
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
                          (vardecl
                            equalsData (fun (con data) (fun (con data) Bool))
                          )
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
                                                    {
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
                                                                                  (all dead (type) [Maybe [[Tuple2 (con bytestring)] (con data)]])
                                                                                }
                                                                                (abs
                                                                                  dead
                                                                                  (type)
                                                                                  [
                                                                                    {
                                                                                      Just
                                                                                      [[Tuple2 (con bytestring)] (con data)]
                                                                                    }
                                                                                    x
                                                                                  ]
                                                                                )
                                                                              ]
                                                                              (abs
                                                                                dead
                                                                                (type)
                                                                                {
                                                                                  Nothing
                                                                                  [[Tuple2 (con bytestring)] (con data)]
                                                                                }
                                                                              )
                                                                            ]
                                                                            (all dead (type) dead)
                                                                          }
                                                                        )
                                                                      )
                                                                    ]
                                                                  )
                                                                ]
                                                                ds
                                                              ]
                                                            ]
                                                            (all dead (type) [Maybe (con data)])
                                                          }
                                                          (lam
                                                            a
                                                            [[Tuple2 (con bytestring)] (con data)]
                                                            (abs
                                                              dead
                                                              (type)
                                                              [
                                                                {
                                                                  Just
                                                                  (con data)
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
                                                                    (con data)
                                                                  }
                                                                  (lam
                                                                    ds
                                                                    (con bytestring)
                                                                    (lam
                                                                      b
                                                                      (con data)
                                                                      b
                                                                    )
                                                                  )
                                                                ]
                                                              ]
                                                            )
                                                          )
                                                        ]
                                                        (abs
                                                          dead
                                                          (type)
                                                          { Nothing (con data) }
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
                                                                TxInInfo_match x
                                                              ]
                                                              [Maybe TxInInfo]
                                                            }
                                                            (lam
                                                              ds
                                                              TxOutRef
                                                              (lam
                                                                ds
                                                                TxOut
                                                                {
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
                                                                        (all dead (type) [Maybe TxInInfo])
                                                                      }
                                                                      (abs
                                                                        dead
                                                                        (type)
                                                                        [
                                                                          {
                                                                            Just
                                                                            TxInInfo
                                                                          }
                                                                          x
                                                                        ]
                                                                      )
                                                                    ]
                                                                    (abs
                                                                      dead
                                                                      (type)
                                                                      {
                                                                        Nothing
                                                                        TxInInfo
                                                                      }
                                                                    )
                                                                  ]
                                                                  (all dead (type) dead)
                                                                }
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
                            snd
                            (all a (type) (all b (type) (fun [[Tuple2 a] b] b)))
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
                          (vardecl
                            txSignedBy (fun TxInfo (fun (con bytestring) Bool))
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
                                                    {
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
                                                                            (all dead (type) [Maybe (con bytestring)])
                                                                          }
                                                                          (abs
                                                                            dead
                                                                            (type)
                                                                            [
                                                                              {
                                                                                Just
                                                                                (con bytestring)
                                                                              }
                                                                              x
                                                                            ]
                                                                          )
                                                                        ]
                                                                        (abs
                                                                          dead
                                                                          (type)
                                                                          {
                                                                            Nothing
                                                                            (con bytestring)
                                                                          }
                                                                        )
                                                                      ]
                                                                      (all dead (type) dead)
                                                                    }
                                                                  )
                                                                ]
                                                                ds
                                                              ]
                                                            ]
                                                            (all dead (type) Bool)
                                                          }
                                                          (lam
                                                            ds
                                                            (con bytestring)
                                                            (abs
                                                              dead (type) True
                                                            )
                                                          )
                                                        ]
                                                        (abs dead (type) False)
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
                                                                (all dead (type) (con integer))
                                                              }
                                                              (abs dead (type) i
                                                              )
                                                            ]
                                                            (abs
                                                              dead
                                                              (type)
                                                              [ go xs ]
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
                                                        Tuple2_match
                                                        (con bytestring)
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
                                                            (all dead (type) (con integer))
                                                          }
                                                          (abs
                                                            dead (type) [ j i ]
                                                          )
                                                        ]
                                                        (abs
                                                          dead (type) [ go xs ]
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
                                        {
                                          [
                                            [
                                              {
                                                [ { Nil_match a } ds ]
                                                (all dead (type) b)
                                              }
                                              (abs dead (type) z)
                                            ]
                                            (lam
                                              y
                                              a
                                              (lam
                                                ys
                                                [List a]
                                                (abs
                                                  dead
                                                  (type)
                                                  [ [ k y ] [ go ys ] ]
                                                )
                                              )
                                            )
                                          ]
                                          (all dead (type) dead)
                                        }
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
                                                                  [
                                                                    TxOut_match
                                                                    e
                                                                  ]
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
                                                                                          (all dead (type) [List [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]])
                                                                                        }
                                                                                        (abs
                                                                                          dead
                                                                                          (type)
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
                                                                                      (abs
                                                                                        dead
                                                                                        (type)
                                                                                        xs
                                                                                      )
                                                                                    ]
                                                                                    (all dead (type) dead)
                                                                                  }
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
                        (let
                          (rec)
                          (termbind
                            (strict)
                            (vardecl
                              checkTxConstraint
                              (fun ScriptContext (fun TxConstraint Bool))
                            )
                            (lam
                              ctx
                              ScriptContext
                              [
                                {
                                  [ ScriptContext_match ctx ]
                                  (fun TxConstraint Bool)
                                }
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
                                                            [
                                                              {
                                                                [
                                                                  TxConstraint_match
                                                                  ds
                                                                ]
                                                                Bool
                                                              }
                                                              (lam
                                                                pubKey
                                                                (con bytestring)
                                                                {
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
                                                                        (all dead (type) Bool)
                                                                      }
                                                                      (abs
                                                                        dead
                                                                        (type)
                                                                        True
                                                                      )
                                                                    ]
                                                                    (abs
                                                                      dead
                                                                      (type)
                                                                      [
                                                                        [
                                                                          {
                                                                            (builtin
                                                                              trace
                                                                            )
                                                                            Bool
                                                                          }
                                                                          (con
                                                                            string
                                                                              "L4"
                                                                          )
                                                                        ]
                                                                        False
                                                                      ]
                                                                    )
                                                                  ]
                                                                  (all dead (type) dead)
                                                                }
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
                                                                    (vardecl
                                                                      j Bool
                                                                    )
                                                                    [
                                                                      [
                                                                        {
                                                                          (builtin
                                                                            trace
                                                                          )
                                                                          Bool
                                                                        }
                                                                        (con
                                                                          string
                                                                            "Lc"
                                                                        )
                                                                      ]
                                                                      False
                                                                    ]
                                                                  )
                                                                  {
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
                                                                          (all dead (type) Bool)
                                                                        }
                                                                        (lam
                                                                          a
                                                                          (con data)
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
                                                                                    (all dead (type) Bool)
                                                                                  }
                                                                                  (abs
                                                                                    dead
                                                                                    (type)
                                                                                    True
                                                                                  )
                                                                                ]
                                                                                (abs
                                                                                  dead
                                                                                  (type)
                                                                                  j
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
                                                                        j
                                                                      )
                                                                    ]
                                                                    (all dead (type) dead)
                                                                  }
                                                                )
                                                              )
                                                            )
                                                          ]
                                                          (lam
                                                            dv
                                                            (con data)
                                                            [
                                                              {
                                                                [
                                                                  TxInfo_match
                                                                  ds
                                                                ]
                                                                Bool
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
                                                                                          (all dead (type) Bool)
                                                                                        }
                                                                                        (abs
                                                                                          dead
                                                                                          (type)
                                                                                          True
                                                                                        )
                                                                                      ]
                                                                                      (abs
                                                                                        dead
                                                                                        (type)
                                                                                        [
                                                                                          [
                                                                                            {
                                                                                              (builtin
                                                                                                trace
                                                                                              )
                                                                                              Bool
                                                                                            }
                                                                                            (con
                                                                                              string
                                                                                                "L2"
                                                                                            )
                                                                                          ]
                                                                                          False
                                                                                        ]
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
                                                                        (all dead (type) Bool)
                                                                      }
                                                                      (abs
                                                                        dead
                                                                        (type)
                                                                        True
                                                                      )
                                                                    ]
                                                                    (abs
                                                                      dead
                                                                      (type)
                                                                      [
                                                                        [
                                                                          {
                                                                            (builtin
                                                                              trace
                                                                            )
                                                                            Bool
                                                                          }
                                                                          (con
                                                                            string
                                                                              "L9"
                                                                          )
                                                                        ]
                                                                        False
                                                                      ]
                                                                    )
                                                                  ]
                                                                  (all dead (type) dead)
                                                                }
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
                                                                  [
                                                                    findDatumHash
                                                                    dv
                                                                  ]
                                                                  ds
                                                                ]
                                                              )
                                                              (termbind
                                                                (nonstrict)
                                                                (vardecl
                                                                  addr
                                                                  Credential
                                                                )
                                                                [
                                                                  ScriptCredential
                                                                  vlh
                                                                ]
                                                              )
                                                              (termbind
                                                                (nonstrict)
                                                                (vardecl
                                                                  addr Address
                                                                )
                                                                [
                                                                  [
                                                                    Address addr
                                                                  ]
                                                                  {
                                                                    Nothing
                                                                    StakingCredential
                                                                  }
                                                                ]
                                                              )
                                                              [
                                                                {
                                                                  [
                                                                    TxInfo_match
                                                                    ds
                                                                  ]
                                                                  Bool
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
                                                                                                            {
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
                                                                                                                    (all dead (type) Bool)
                                                                                                                  }
                                                                                                                  (lam
                                                                                                                    svh
                                                                                                                    (con bytestring)
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
                                                                                                                                      checkBinRel
                                                                                                                                      equalsInteger
                                                                                                                                    ]
                                                                                                                                    ds
                                                                                                                                  ]
                                                                                                                                  vl
                                                                                                                                ]
                                                                                                                              ]
                                                                                                                              (all dead (type) Bool)
                                                                                                                            }
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
                                                                                                                                          (con bytestring)
                                                                                                                                        }
                                                                                                                                        hsh
                                                                                                                                      ]
                                                                                                                                      (all dead (type) Bool)
                                                                                                                                    }
                                                                                                                                    (lam
                                                                                                                                      a
                                                                                                                                      (con bytestring)
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
                                                                                                                                                (all dead (type) Bool)
                                                                                                                                              }
                                                                                                                                              (abs
                                                                                                                                                dead
                                                                                                                                                (type)
                                                                                                                                                [
                                                                                                                                                  [
                                                                                                                                                    fEqAddress_c
                                                                                                                                                    ds
                                                                                                                                                  ]
                                                                                                                                                  addr
                                                                                                                                                ]
                                                                                                                                              )
                                                                                                                                            ]
                                                                                                                                            (abs
                                                                                                                                              dead
                                                                                                                                              (type)
                                                                                                                                              False
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
                                                                                                                                    False
                                                                                                                                  )
                                                                                                                                ]
                                                                                                                                (all dead (type) dead)
                                                                                                                              }
                                                                                                                            )
                                                                                                                          ]
                                                                                                                          (abs
                                                                                                                            dead
                                                                                                                            (type)
                                                                                                                            False
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
                                                                                                                  False
                                                                                                                )
                                                                                                              ]
                                                                                                              (all dead (type) dead)
                                                                                                            }
                                                                                                          )
                                                                                                        )
                                                                                                      )
                                                                                                    ]
                                                                                                  )
                                                                                                ]
                                                                                                ds
                                                                                              ]
                                                                                            ]
                                                                                            (all dead (type) Bool)
                                                                                          }
                                                                                          (abs
                                                                                            dead
                                                                                            (type)
                                                                                            True
                                                                                          )
                                                                                        ]
                                                                                        (abs
                                                                                          dead
                                                                                          (type)
                                                                                          [
                                                                                            [
                                                                                              {
                                                                                                (builtin
                                                                                                  trace
                                                                                                )
                                                                                                Bool
                                                                                              }
                                                                                              (con
                                                                                                string
                                                                                                  "Lb"
                                                                                              )
                                                                                            ]
                                                                                            False
                                                                                          ]
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
                                                        {
                                                          [
                                                            [
                                                              {
                                                                [
                                                                  Bool_match
                                                                  [
                                                                    [
                                                                      [
                                                                        checkBinRel
                                                                        lessThanEqualsInteger
                                                                      ]
                                                                      vl
                                                                    ]
                                                                    [
                                                                      [
                                                                        valuePaidTo
                                                                        ds
                                                                      ]
                                                                      pk
                                                                    ]
                                                                  ]
                                                                ]
                                                                (all dead (type) Bool)
                                                              }
                                                              (abs
                                                                dead (type) True
                                                              )
                                                            ]
                                                            (abs
                                                              dead
                                                              (type)
                                                              [
                                                                [
                                                                  {
                                                                    (builtin
                                                                      trace
                                                                    )
                                                                    Bool
                                                                  }
                                                                  (con
                                                                    string "La"
                                                                  )
                                                                ]
                                                                False
                                                              ]
                                                            )
                                                          ]
                                                          (all dead (type) dead)
                                                        }
                                                      )
                                                    )
                                                  ]
                                                  (lam
                                                    vl
                                                    [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                    {
                                                      [
                                                        [
                                                          {
                                                            [
                                                              Bool_match
                                                              [
                                                                [
                                                                  [
                                                                    checkBinRel
                                                                    lessThanEqualsInteger
                                                                  ]
                                                                  vl
                                                                ]
                                                                [
                                                                  valueProduced
                                                                  ds
                                                                ]
                                                              ]
                                                            ]
                                                            (all dead (type) Bool)
                                                          }
                                                          (abs dead (type) True)
                                                        ]
                                                        (abs
                                                          dead
                                                          (type)
                                                          [
                                                            [
                                                              {
                                                                (builtin trace)
                                                                Bool
                                                              }
                                                              (con string "L6")
                                                            ]
                                                            False
                                                          ]
                                                        )
                                                      ]
                                                      (all dead (type) dead)
                                                    }
                                                  )
                                                ]
                                                (lam
                                                  xs
                                                  [List TxConstraint]
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
                                                                    TxConstraint
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
                                                                  checkTxConstraint
                                                                  ctx
                                                                ]
                                                              ]
                                                              xs
                                                            ]
                                                          ]
                                                          (all dead (type) Bool)
                                                        }
                                                        (abs dead (type) True)
                                                      ]
                                                      (abs
                                                        dead
                                                        (type)
                                                        [
                                                          [
                                                            {
                                                              (builtin trace)
                                                              Bool
                                                            }
                                                            (con string "Ld")
                                                          ]
                                                          False
                                                        ]
                                                      )
                                                    ]
                                                    (all dead (type) dead)
                                                  }
                                                )
                                              ]
                                              (lam
                                                vl
                                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                {
                                                  [
                                                    [
                                                      {
                                                        [
                                                          Bool_match
                                                          [
                                                            [
                                                              [
                                                                checkBinRel
                                                                lessThanEqualsInteger
                                                              ]
                                                              vl
                                                            ]
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
                                                        (all dead (type) Bool)
                                                      }
                                                      (abs dead (type) True)
                                                    ]
                                                    (abs
                                                      dead
                                                      (type)
                                                      [
                                                        [
                                                          {
                                                            (builtin trace) Bool
                                                          }
                                                          (con string "L5")
                                                        ]
                                                        False
                                                      ]
                                                    )
                                                  ]
                                                  (all dead (type) dead)
                                                }
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
                                                      { (builtin trace) Bool }
                                                      (con string "L7")
                                                    ]
                                                    False
                                                  ]
                                                )
                                                {
                                                  [
                                                    [
                                                      {
                                                        [
                                                          {
                                                            Maybe_match TxInInfo
                                                          }
                                                          [
                                                            [
                                                              findTxInByTxOutRef
                                                              txOutRef
                                                            ]
                                                            ds
                                                          ]
                                                        ]
                                                        (all dead (type) Bool)
                                                      }
                                                      (lam
                                                        a
                                                        TxInInfo
                                                        (abs
                                                          dead
                                                          (type)
                                                          [
                                                            {
                                                              [
                                                                TxInInfo_match a
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
                                                                        {
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
                                                                                (all dead (type) Bool)
                                                                              }
                                                                              (lam
                                                                                ds
                                                                                (con bytestring)
                                                                                (abs
                                                                                  dead
                                                                                  (type)
                                                                                  j
                                                                                )
                                                                              )
                                                                            ]
                                                                            (abs
                                                                              dead
                                                                              (type)
                                                                              True
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
                                                          ]
                                                        )
                                                      )
                                                    ]
                                                    (abs dead (type) j)
                                                  ]
                                                  (all dead (type) dead)
                                                }
                                              )
                                            )
                                          ]
                                          (lam
                                            txOutRef
                                            TxOutRef
                                            (lam
                                              ds
                                              (con data)
                                              {
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
                                                      (all dead (type) Bool)
                                                    }
                                                    (lam
                                                      ds
                                                      TxInInfo
                                                      (abs dead (type) True)
                                                    )
                                                  ]
                                                  (abs
                                                    dead
                                                    (type)
                                                    [
                                                      [
                                                        { (builtin trace) Bool }
                                                        (con string "L8")
                                                      ]
                                                      False
                                                    ]
                                                  )
                                                ]
                                                (all dead (type) dead)
                                              }
                                            )
                                          )
                                        ]
                                        (lam
                                          interval
                                          [Interval (con integer)]
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
                                                            contains
                                                            (con integer)
                                                          }
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
                                                  (all dead (type) Bool)
                                                }
                                                (abs dead (type) True)
                                              ]
                                              (abs
                                                dead
                                                (type)
                                                [
                                                  [
                                                    { (builtin trace) Bool }
                                                    (con string "L3")
                                                  ]
                                                  False
                                                ]
                                              )
                                            ]
                                            (all dead (type) dead)
                                          }
                                        )
                                      ]
                                    )
                                  )
                                )
                              ]
                            )
                          )
                          (let
                            (nonrec)
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
                                          {
                                            [
                                              { { TxConstraints_match i } o } ds
                                            ]
                                            Bool
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
                                                (let
                                                  (nonrec)
                                                  (termbind
                                                    (nonstrict)
                                                    (vardecl j Bool)
                                                    [
                                                      [
                                                        { (builtin trace) Bool }
                                                        (con string "Ld")
                                                      ]
                                                      False
                                                    ]
                                                  )
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
                                                                    TxConstraint
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
                                                                  checkTxConstraint
                                                                  ptx
                                                                ]
                                                              ]
                                                              ds
                                                            ]
                                                          ]
                                                          (all dead (type) Bool)
                                                        }
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
                                                                  (all dead (type) Bool)
                                                                }
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
                                                                          (all dead (type) Bool)
                                                                        }
                                                                        (abs
                                                                          dead
                                                                          (type)
                                                                          True
                                                                        )
                                                                      ]
                                                                      (abs
                                                                        dead
                                                                        (type)
                                                                        j
                                                                      )
                                                                    ]
                                                                    (all dead (type) dead)
                                                                  }
                                                                )
                                                              ]
                                                              (abs dead (type) j
                                                              )
                                                            ]
                                                            (all dead (type) dead)
                                                          }
                                                        )
                                                      ]
                                                      (abs dead (type) j)
                                                    ]
                                                    (all dead (type) dead)
                                                  }
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
                                                {
                                                  Tuple2_match (con bytestring)
                                                }
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
                                                                    (con
                                                                      integer 0
                                                                    )
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
                                                  { (builtin trace) Unit }
                                                  (con string "Lg")
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
                                  {
                                    [
                                      [
                                        {
                                          [
                                            { Maybe_match TxInInfo }
                                            [ findOwnInput ds ]
                                          ]
                                          (all dead (type) [[Tuple2 (con bytestring)] (con bytestring)])
                                        }
                                        (lam
                                          ds
                                          TxInInfo
                                          (abs
                                            dead
                                            (type)
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
                                                              [
                                                                Address_match ds
                                                              ]
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
                                                                          (error
                                                                            e
                                                                          )
                                                                        )
                                                                      ]
                                                                    )
                                                                  ]
                                                                  (lam
                                                                    s
                                                                    (con bytestring)
                                                                    {
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
                                                                            (all dead (type) [[Tuple2 (con bytestring)] (con bytestring)])
                                                                          }
                                                                          (lam
                                                                            dh
                                                                            (con bytestring)
                                                                            (abs
                                                                              dead
                                                                              (type)
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
                                                                        (abs
                                                                          dead
                                                                          (type)
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
                                                                      (all dead (type) dead)
                                                                    }
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
                                      (abs
                                        dead
                                        (type)
                                        [ fail (abs e (type) (error e)) ]
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
                                ownHash (fun ScriptContext (con bytestring))
                              )
                              (lam
                                p
                                ScriptContext
                                [
                                  {
                                    [
                                      {
                                        { Tuple2_match (con bytestring) }
                                        (con bytestring)
                                      }
                                      [ ownHashes p ]
                                    ]
                                    (con bytestring)
                                  }
                                  (lam
                                    a
                                    (con bytestring)
                                    (lam ds (con bytestring) a)
                                  )
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
                                {
                                  [
                                    [
                                      {
                                        [ { Maybe_match ThreadToken } m ]
                                        (all dead (type) (fun (con bytestring) [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]))
                                      }
                                      (lam
                                        a
                                        ThreadToken
                                        (abs
                                          dead
                                          (type)
                                          (let
                                            (nonrec)
                                            (termbind
                                              (nonstrict)
                                              (vardecl currency (con bytestring)
                                              )
                                              [
                                                {
                                                  [ ThreadToken_match a ]
                                                  (con bytestring)
                                                }
                                                (lam
                                                  ds
                                                  TxOutRef
                                                  (lam ds (con bytestring) ds)
                                                )
                                              ]
                                            )
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
                                                        {
                                                          Tuple2
                                                          (con bytestring)
                                                        }
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
                                                              {
                                                                Tuple2
                                                                (con bytestring)
                                                              }
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
                                    (abs dead (type) b)
                                  ]
                                  (all dead (type) dead)
                                }
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
                                                      {
                                                        [
                                                          [
                                                            {
                                                              [
                                                                {
                                                                  Maybe_match
                                                                  TxInInfo
                                                                }
                                                                [
                                                                  findOwnInput w
                                                                ]
                                                              ]
                                                              (all dead (type) [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]])
                                                            }
                                                            (lam
                                                              a
                                                              TxInInfo
                                                              (abs
                                                                dead
                                                                (type)
                                                                [
                                                                  {
                                                                    [
                                                                      TxInInfo_match
                                                                      a
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
                                                            )
                                                          ]
                                                          (abs
                                                            dead
                                                            (type)
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
                                                                            trace
                                                                          )
                                                                          Unit
                                                                        }
                                                                        (con
                                                                          string
                                                                            "S0"
                                                                        )
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
                                                        (all dead (type) dead)
                                                      }
                                                    )
                                                    (termbind
                                                      (nonstrict)
                                                      (vardecl j Bool)
                                                      {
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
                                                                      [
                                                                        {
                                                                          State
                                                                          s
                                                                        }
                                                                        w
                                                                      ]
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
                                                                              integer
                                                                                -1
                                                                            )
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
                                                                  ]
                                                                  w
                                                                ]
                                                              ]
                                                              (all dead (type) Bool)
                                                            }
                                                            (lam
                                                              ds
                                                              [[Tuple2 [[TxConstraints Void] Void]] [State s]]
                                                              (abs
                                                                dead
                                                                (type)
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
                                                                            {
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
                                                                                    (all dead (type) Bool)
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
                                                                                          j
                                                                                          Bool
                                                                                        )
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
                                                                                                            checkScriptContext
                                                                                                            Void
                                                                                                          }
                                                                                                          Void
                                                                                                        }
                                                                                                        fToDataVoid_ctoBuiltinData
                                                                                                      ]
                                                                                                      newConstraints
                                                                                                    ]
                                                                                                    w
                                                                                                  ]
                                                                                                ]
                                                                                                (all dead (type) Bool)
                                                                                              }
                                                                                              (abs
                                                                                                dead
                                                                                                (type)
                                                                                                True
                                                                                              )
                                                                                            ]
                                                                                            (abs
                                                                                              dead
                                                                                              (type)
                                                                                              [
                                                                                                [
                                                                                                  {
                                                                                                    (builtin
                                                                                                      trace
                                                                                                    )
                                                                                                    Bool
                                                                                                  }
                                                                                                  (con
                                                                                                    string
                                                                                                      "S4"
                                                                                                  )
                                                                                                ]
                                                                                                False
                                                                                              ]
                                                                                            )
                                                                                          ]
                                                                                          (all dead (type) dead)
                                                                                        }
                                                                                      )
                                                                                      {
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
                                                                                              (all dead (type) Bool)
                                                                                            }
                                                                                            (abs
                                                                                              dead
                                                                                              (type)
                                                                                              j
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
                                                                                                          {
                                                                                                            (builtin
                                                                                                              trace
                                                                                                            )
                                                                                                            Bool
                                                                                                          }
                                                                                                          (con
                                                                                                            string
                                                                                                              "S3"
                                                                                                          )
                                                                                                        ]
                                                                                                        False
                                                                                                      ]
                                                                                                    ]
                                                                                                    (all dead (type) Bool)
                                                                                                  }
                                                                                                  (abs
                                                                                                    dead
                                                                                                    (type)
                                                                                                    j
                                                                                                  )
                                                                                                ]
                                                                                                (abs
                                                                                                  dead
                                                                                                  (type)
                                                                                                  False
                                                                                                )
                                                                                              ]
                                                                                              (all dead (type) dead)
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
                                                                                          (all dead (type) Bool)
                                                                                        }
                                                                                        (abs
                                                                                          dead
                                                                                          (type)
                                                                                          True
                                                                                        )
                                                                                      ]
                                                                                      (abs
                                                                                        dead
                                                                                        (type)
                                                                                        [
                                                                                          [
                                                                                            {
                                                                                              (builtin
                                                                                                trace
                                                                                              )
                                                                                              Bool
                                                                                            }
                                                                                            (con
                                                                                              string
                                                                                                "S5"
                                                                                            )
                                                                                          ]
                                                                                          False
                                                                                        ]
                                                                                      )
                                                                                    ]
                                                                                    (all dead (type) dead)
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
                                                            )
                                                          ]
                                                          (abs
                                                            dead
                                                            (type)
                                                            [
                                                              [
                                                                {
                                                                  (builtin trace
                                                                  )
                                                                  Bool
                                                                }
                                                                (con string "S6"
                                                                )
                                                              ]
                                                              False
                                                            ]
                                                          )
                                                        ]
                                                        (all dead (type) dead)
                                                      }
                                                    )
                                                    (termbind
                                                      (nonstrict)
                                                      (vardecl j Bool)
                                                      {
                                                        [
                                                          [
                                                            {
                                                              [
                                                                {
                                                                  Maybe_match
                                                                  ThreadToken
                                                                }
                                                                ww
                                                              ]
                                                              (all dead (type) Bool)
                                                            }
                                                            (lam
                                                              threadToken
                                                              ThreadToken
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
                                                                        (all dead (type) Bool)
                                                                      }
                                                                      (abs
                                                                        dead
                                                                        (type)
                                                                        j
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
                                                                                    {
                                                                                      (builtin
                                                                                        trace
                                                                                      )
                                                                                      Bool
                                                                                    }
                                                                                    (con
                                                                                      string
                                                                                        "S2"
                                                                                    )
                                                                                  ]
                                                                                  False
                                                                                ]
                                                                              ]
                                                                              (all dead (type) Bool)
                                                                            }
                                                                            (abs
                                                                              dead
                                                                              (type)
                                                                              j
                                                                            )
                                                                          ]
                                                                          (abs
                                                                            dead
                                                                            (type)
                                                                            False
                                                                          )
                                                                        ]
                                                                        (all dead (type) dead)
                                                                      }
                                                                    )
                                                                  ]
                                                                  (all dead (type) dead)
                                                                }
                                                              )
                                                            )
                                                          ]
                                                          (abs dead (type) j)
                                                        ]
                                                        (all dead (type) dead)
                                                      }
                                                    )
                                                    {
                                                      [
                                                        [
                                                          {
                                                            [
                                                              Bool_match
                                                              [
                                                                [ [ ww w ] w ] w
                                                              ]
                                                            ]
                                                            (all dead (type) Bool)
                                                          }
                                                          (abs dead (type) j)
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
                                                                        {
                                                                          (builtin
                                                                            trace
                                                                          )
                                                                          Bool
                                                                        }
                                                                        (con
                                                                          string
                                                                            "S1"
                                                                        )
                                                                      ]
                                                                      False
                                                                    ]
                                                                  ]
                                                                  (all dead (type) Bool)
                                                                }
                                                                (abs
                                                                  dead (type) j
                                                                )
                                                              ]
                                                              (abs
                                                                dead
                                                                (type)
                                                                False
                                                              )
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
                                                [
                                                  { { StateMachine_match s } i }
                                                  w
                                                ]
                                                Bool
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
                                                                        {
                                                                          wmkValidator
                                                                          s
                                                                        }
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
                              (nonstrict)
                              (vardecl
                                mkValidator
                                (fun GameState (fun GameInput (fun ScriptContext Bool)))
                              )
                              [
                                [
                                  { { mkValidator GameState } GameInput }
                                  fToDataGameState_ctoBuiltinData
                                ]
                                machine
                              ]
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
        )
      )
    )
  )
)