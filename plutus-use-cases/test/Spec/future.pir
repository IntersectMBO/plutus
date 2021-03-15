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
          (datatype (tyvardecl Unit (type))  Unit_match (vardecl Unit Unit))
        )
        (datatypebind
          (datatype
            (tyvardecl Bool (type))

            Bool_match
            (vardecl True Bool) (vardecl False Bool)
          )
        )
        (termbind
          (strict)
          (vardecl equalsInteger (fun (con integer) (fun (con integer) Bool)))
          (lam
            arg
            (con integer)
            (lam
              arg
              (con integer)
              [
                (lam
                  b
                  (con bool)
                  [ [ [ { (builtin ifThenElse) Bool } b ] True ] False ]
                )
                [ [ (builtin equalsInteger) arg ] arg ]
              ]
            )
          )
        )
        (datatypebind
          (datatype
            (tyvardecl Tuple3 (fun (type) (fun (type) (fun (type) (type)))))
            (tyvardecl a (type)) (tyvardecl b (type)) (tyvardecl c (type))
            Tuple3_match
            (vardecl Tuple3 (fun a (fun b (fun c [[[Tuple3 a] b] c]))))
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
            (tyvardecl Maybe (fun (type) (type)))
            (tyvardecl a (type))
            Maybe_match
            (vardecl Just (fun a [Maybe a])) (vardecl Nothing [Maybe a])
          )
        )
        (datatypebind
          (datatype
            (tyvardecl TxInInfo (type))

            TxInInfo_match
            (vardecl
              TxInInfo
              (fun TxOutRef (fun [Maybe [[[Tuple3 (con bytestring)] (con bytestring)] (con bytestring)]] (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] TxInInfo)))
            )
          )
        )
        (datatypebind
          (datatype
            (tyvardecl Address (type))

            Address_match
            (vardecl PubKeyAddress (fun (con bytestring) Address))
            (vardecl ScriptAddress (fun (con bytestring) Address))
          )
        )
        (datatypebind
          (datatype
            (tyvardecl TxOutType (type))

            TxOutType_match
            (vardecl PayToPubKey TxOutType)
            (vardecl PayToScript (fun (con bytestring) TxOutType))
          )
        )
        (datatypebind
          (datatype
            (tyvardecl TxOut (type))

            TxOut_match
            (vardecl
              TxOut
              (fun Address (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun TxOutType TxOut)))
            )
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
        (let
          (rec)
          (datatypebind
            (datatype
              (tyvardecl Data (type))

              Data_match
              (vardecl B (fun (con bytestring) Data))
              (vardecl Constr (fun (con integer) (fun [List Data] Data)))
              (vardecl I (fun (con integer) Data))
              (vardecl List (fun [List Data] Data))
              (vardecl Map (fun [List [[Tuple2 Data] Data]] Data))
            )
          )
          (let
            (nonrec)
            (datatypebind
              (datatype
                (tyvardecl TxInfo (type))

                TxInfo_match
                (vardecl
                  TxInfo
                  (fun [List TxInInfo] (fun [List TxOut] (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun [Interval (con integer)] (fun [List (con bytestring)] (fun [List (con bytestring)] (fun [List [[Tuple2 (con bytestring)] Data]] (fun (con bytestring) TxInfo)))))))))
                )
              )
            )
            (datatypebind
              (datatype
                (tyvardecl ValidatorCtx (type))

                ValidatorCtx_match
                (vardecl
                  ValidatorCtx (fun TxInfo (fun (con integer) ValidatorCtx))
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
                (vardecl
                  InputConstraint (fun a (fun TxOutRef [InputConstraint a]))
                )
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
                  MustForgeValue
                  (fun (con bytestring) (fun (con bytestring) (fun (con integer) TxConstraint)))
                )
                (vardecl
                  MustHashDatum (fun (con bytestring) (fun Data TxConstraint))
                )
                (vardecl MustIncludeDatum (fun Data TxConstraint))
                (vardecl
                  MustPayToOtherScript
                  (fun (con bytestring) (fun Data (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] TxConstraint)))
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
                  MustSpendScriptOutput (fun TxOutRef (fun Data TxConstraint))
                )
                (vardecl
                  MustValidateIn (fun [Interval (con integer)] TxConstraint)
                )
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
                  (fun (fun [State s] (fun i [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State s]]])) (fun (fun s Bool) (fun (fun s (fun i (fun ValidatorCtx Bool))) [[StateMachine s] i])))
                )
              )
            )
            (termbind
              (strict)
              (vardecl
                mkStateMachine
                (all s (type) (all i (type) (fun s (fun i (fun ValidatorCtx Bool)))))
              )
              (abs
                s
                (type)
                (abs i (type) (lam ds s (lam ds i (lam ds ValidatorCtx True))))
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
            (let
              (rec)
              (termbind
                (nonstrict)
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
                          [
                            [
                              [
                                { [ { Nil_match a } l ] (fun Unit b) }
                                (lam thunk Unit acc)
                              ]
                              (lam
                                x
                                a
                                (lam
                                  xs
                                  [List a]
                                  (lam
                                    thunk
                                    Unit
                                    [
                                      [ f x ]
                                      [ [ [ { { foldr a } b } f ] acc ] xs ]
                                    ]
                                  )
                                )
                              )
                            ]
                            Unit
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
                    mustPayToOtherScript
                    (all i (type) (all o (type) (fun (con bytestring) (fun Data (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] [[TxConstraints i] o])))))
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
                          Data
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
                                                [ c [ MustIncludeDatum dv ] ] n
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
                                                    [ MustPayToOtherScript vh ]
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
                    equalsByteString
                    (fun (con bytestring) (fun (con bytestring) Bool))
                  )
                  (lam
                    arg
                    (con bytestring)
                    (lam
                      arg
                      (con bytestring)
                      [
                        (lam
                          b
                          (con bool)
                          [ [ [ { (builtin ifThenElse) Bool } b ] True ] False ]
                        )
                        [ [ (builtin equalsByteString) arg ] arg ]
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
                      [
                        [
                          [
                            { [ Bool_match ds ] (fun Unit Bool) }
                            (lam thunk Unit True)
                          ]
                          (lam thunk Unit ds)
                        ]
                        Unit
                      ]
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
                    (nonstrict)
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
                                [
                                  [
                                    [
                                      { [ { Nil_match a } ds ] (fun Unit m) }
                                      (lam thunk Unit [ { mempty m } dMonoid ])
                                    ]
                                    (lam
                                      x
                                      a
                                      (lam
                                        xs
                                        [List a]
                                        (lam
                                          thunk
                                          Unit
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
                                  Unit
                                ]
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
                      (nonstrict)
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
                              [
                                [
                                  [
                                    {
                                      [ { Nil_match a } l ] (fun Unit [List b])
                                    }
                                    (lam thunk Unit { Nil b })
                                  ]
                                  (lam
                                    x
                                    a
                                    (lam
                                      xs
                                      [List a]
                                      (lam
                                        thunk
                                        Unit
                                        [
                                          [ { Cons b } [ f x ] ]
                                          [
                                            [ { { fFunctorNil_cfmap a } b } f ]
                                            xs
                                          ]
                                        ]
                                      )
                                    )
                                  )
                                ]
                                Unit
                              ]
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
                                              {
                                                fFunctorNil_cfmap [[Tuple2 k] r]
                                              }
                                              [[Tuple2 k] [[These v] r]]
                                            }
                                            (lam
                                              ds
                                              [[Tuple2 k] r]
                                              [
                                                {
                                                  [
                                                    { { Tuple2_match k } r } ds
                                                  ]
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
                                                          { Tuple2 k }
                                                          [[These v] r]
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
                                                          {
                                                            { Tuple2_match k } r
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
                                                          [
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
                                                                  (fun Unit [List [[Tuple2 k] r]])
                                                                }
                                                                (lam
                                                                  thunk Unit xs
                                                                )
                                                              ]
                                                              (lam
                                                                thunk
                                                                Unit
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
                                                            Unit
                                                          ]
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
                                                        [
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
                                                                (fun Unit [[These v] r])
                                                              }
                                                              (lam
                                                                thunk
                                                                Unit
                                                                [
                                                                  {
                                                                    { This v } r
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
                                                                (lam
                                                                  thunk
                                                                  Unit
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
                                                                        [
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
                                                                                (fun Unit [[These v] r])
                                                                              }
                                                                              (lam
                                                                                thunk
                                                                                Unit
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
                                                                            (lam
                                                                              thunk
                                                                              Unit
                                                                              [
                                                                                go
                                                                                xs
                                                                              ]
                                                                            )
                                                                          ]
                                                                          Unit
                                                                        ]
                                                                      )
                                                                    )
                                                                  ]
                                                                )
                                                              )
                                                            )
                                                          ]
                                                          Unit
                                                        ]
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
                                  [
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
                                          (fun Unit [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]]])
                                        }
                                        (lam
                                          thunk
                                          Unit
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
                                          (lam
                                            thunk
                                            Unit
                                            [
                                              {
                                                [
                                                  {
                                                    {
                                                      Tuple2_match
                                                      (con bytestring)
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
                                                                      [
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
                                                                              (fun Unit [List [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]])
                                                                            }
                                                                            (lam
                                                                              thunk
                                                                              Unit
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
                                                                              (lam
                                                                                thunk
                                                                                Unit
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
                                                                        Unit
                                                                      ]
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
                                                                  [
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
                                                                          (fun Unit [List [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]])
                                                                        }
                                                                        (lam
                                                                          thunk
                                                                          Unit
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
                                                                          (lam
                                                                            thunk
                                                                            Unit
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
                                                                    Unit
                                                                  ]
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
                                    Unit
                                  ]
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
                                    [
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
                                            (fun Unit [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]])
                                          }
                                          (lam
                                            thunk
                                            Unit
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
                                            (lam
                                              thunk
                                              Unit
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
                                                          [
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
                                                                  (fun Unit [List [[Tuple2 (con bytestring)] (con integer)]])
                                                                }
                                                                (lam
                                                                  thunk
                                                                  Unit
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
                                                                  (lam
                                                                    thunk
                                                                    Unit
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
                                                            Unit
                                                          ]
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
                                      Unit
                                    ]
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
                          fAdditiveMonoidValue
                          (fun [(lam a (type) a) [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]] (fun [(lam a (type) a) [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]))
                        )
                        (lam
                          ds
                          [(lam a (type) a) [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                          (lam
                            ds
                            [(lam a (type) a) [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                            [ [ [ unionWith (builtin addInteger) ] ds ] ds ]
                          )
                        )
                      )
                      (termbind
                        (nonstrict)
                        (vardecl unitDatum Data)
                        [ [ Constr (con integer 0) ] { Nil Data } ]
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
                      (datatypebind
                        (datatype
                          (tyvardecl Role (type))

                          Role_match
                          (vardecl Long Role) (vardecl Short Role)
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
                                  [
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
                                          (fun Unit [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]])
                                        }
                                        (lam
                                          thunk
                                          Unit
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
                                          (lam
                                            thunk
                                            Unit
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
                                                        [
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
                                                                (fun Unit [List [[Tuple2 (con bytestring)] (con integer)]])
                                                              }
                                                              (lam
                                                                thunk
                                                                Unit
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
                                                                (lam
                                                                  thunk
                                                                  Unit
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
                                                          Unit
                                                        ]
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
                                    Unit
                                  ]
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
                              [ [ unionWith (builtin addInteger) ] ds ]
                              [
                                [ fAdditiveGroupValue_cscale (con integer -1) ]
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
                                          [ { { TxConstraints_match i } o } l ]
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
                                                      foldr [InputConstraint i]
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
                                                          TxConstraints_match i
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
                                                  { foldr [OutputConstraint o] }
                                                  [List [OutputConstraint o]]
                                                }
                                                { Cons [OutputConstraint o] }
                                              ]
                                              [
                                                {
                                                  [
                                                    {
                                                      { TxConstraints_match i }
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
                                [ Payouts_match ds ] [[TxConstraints Void] Void]
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
                                                    fMonoidTxConstraints_c Void
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
                                  { { TxConstraints i } o } { Nil TxConstraint }
                                ]
                                { Nil [InputConstraint i] }
                              ]
                              { Nil [OutputConstraint o] }
                            ]
                          )
                        )
                      )
                      (termbind
                        (strict)
                        (vardecl
                          fIsDataByteString_cfromData
                          (fun Data [Maybe (con bytestring)])
                        )
                        (lam
                          ds
                          Data
                          [
                            [
                              [
                                [
                                  [
                                    [
                                      {
                                        [ Data_match ds ]
                                        (fun Unit [Maybe (con bytestring)])
                                      }
                                      (lam
                                        b
                                        (con bytestring)
                                        (lam
                                          thunk
                                          Unit
                                          [ { Just (con bytestring) } b ]
                                        )
                                      )
                                    ]
                                    (lam
                                      default_arg0
                                      (con integer)
                                      (lam
                                        default_arg1
                                        [List Data]
                                        (lam
                                          thunk
                                          Unit
                                          { Nothing (con bytestring) }
                                        )
                                      )
                                    )
                                  ]
                                  (lam
                                    default_arg0
                                    (con integer)
                                    (lam thunk Unit { Nothing (con bytestring) }
                                    )
                                  )
                                ]
                                (lam
                                  default_arg0
                                  [List Data]
                                  (lam thunk Unit { Nothing (con bytestring) })
                                )
                              ]
                              (lam
                                default_arg0
                                [List [[Tuple2 Data] Data]]
                                (lam thunk Unit { Nothing (con bytestring) })
                              )
                            ]
                            Unit
                          ]
                        )
                      )
                      (datatypebind
                        (datatype
                          (tyvardecl IsData (fun (type) (type)))
                          (tyvardecl a (type))
                          IsData_match
                          (vardecl
                            CConsIsData
                            (fun (fun a Data) (fun (fun Data [Maybe a]) [IsData a]))
                          )
                        )
                      )
                      (termbind
                        (nonstrict)
                        (vardecl fIsDataCurrencySymbol [IsData (con bytestring)]
                        )
                        [
                          [ { CConsIsData (con bytestring) } B ]
                          fIsDataByteString_cfromData
                        ]
                      )
                      (termbind
                        (strict)
                        (vardecl
                          fIsDataInteger_cfromData
                          (fun Data [Maybe (con integer)])
                        )
                        (lam
                          ds
                          Data
                          [
                            [
                              [
                                [
                                  [
                                    [
                                      {
                                        [ Data_match ds ]
                                        (fun Unit [Maybe (con integer)])
                                      }
                                      (lam
                                        default_arg0
                                        (con bytestring)
                                        (lam
                                          thunk Unit { Nothing (con integer) }
                                        )
                                      )
                                    ]
                                    (lam
                                      default_arg0
                                      (con integer)
                                      (lam
                                        default_arg1
                                        [List Data]
                                        (lam
                                          thunk Unit { Nothing (con integer) }
                                        )
                                      )
                                    )
                                  ]
                                  (lam
                                    i
                                    (con integer)
                                    (lam thunk Unit [ { Just (con integer) } i ]
                                    )
                                  )
                                ]
                                (lam
                                  default_arg0
                                  [List Data]
                                  (lam thunk Unit { Nothing (con integer) })
                                )
                              ]
                              (lam
                                default_arg0
                                [List [[Tuple2 Data] Data]]
                                (lam thunk Unit { Nothing (con integer) })
                              )
                            ]
                            Unit
                          ]
                        )
                      )
                      (termbind
                        (nonstrict)
                        (vardecl fIsDataInteger [IsData (con integer)])
                        [
                          [ { CConsIsData (con integer) } I ]
                          fIsDataInteger_cfromData
                        ]
                      )
                      (termbind
                        (strict)
                        (vardecl
                          fApplicativeMaybe_c
                          (all a (type) (all b (type) (fun [Maybe (fun a b)] (fun [Maybe a] [Maybe b]))))
                        )
                        (abs
                          a
                          (type)
                          (abs
                            b
                            (type)
                            (lam
                              ds
                              [Maybe (fun a b)]
                              (lam
                                ds
                                [Maybe a]
                                [
                                  [
                                    [
                                      {
                                        [ { Maybe_match (fun a b) } ds ]
                                        (fun Unit [Maybe b])
                                      }
                                      (lam
                                        ipv
                                        (fun a b)
                                        (lam
                                          thunk
                                          Unit
                                          [
                                            [
                                              [
                                                {
                                                  [ { Maybe_match a } ds ]
                                                  (fun Unit [Maybe b])
                                                }
                                                (lam
                                                  ipv
                                                  a
                                                  (lam
                                                    thunk
                                                    Unit
                                                    [ { Just b } [ ipv ipv ] ]
                                                  )
                                                )
                                              ]
                                              (lam thunk Unit { Nothing b })
                                            ]
                                            Unit
                                          ]
                                        )
                                      )
                                    ]
                                    (lam thunk Unit { Nothing b })
                                  ]
                                  Unit
                                ]
                              )
                            )
                          )
                        )
                      )
                      (termbind
                        (strict)
                        (vardecl
                          fFunctorMaybe_cfmap
                          (all a (type) (all b (type) (fun (fun a b) (fun [Maybe a] [Maybe b]))))
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
                                ds
                                [Maybe a]
                                [
                                  [
                                    [
                                      {
                                        [ { Maybe_match a } ds ]
                                        (fun Unit [Maybe b])
                                      }
                                      (lam
                                        a
                                        a
                                        (lam thunk Unit [ { Just b } [ f a ] ])
                                      )
                                    ]
                                    (lam thunk Unit { Nothing b })
                                  ]
                                  Unit
                                ]
                              )
                            )
                          )
                        )
                      )
                      (datatypebind
                        (datatype
                          (tyvardecl
                            Applicative (fun (fun (type) (type)) (type))
                          )
                          (tyvardecl f (fun (type) (type)))
                          Applicative_match
                          (vardecl
                            CConsApplicative
                            (fun [(lam f (fun (type) (type)) (all a (type) (all b (type) (fun (fun a b) (fun [f a] [f b]))))) f] (fun (all a (type) (fun a [f a])) (fun (all a (type) (all b (type) (fun [f (fun a b)] (fun [f a] [f b])))) [Applicative f])))
                          )
                        )
                      )
                      (termbind
                        (nonstrict)
                        (vardecl fApplicativeMaybe [Applicative Maybe])
                        [
                          [
                            [ { CConsApplicative Maybe } fFunctorMaybe_cfmap ]
                            Just
                          ]
                          fApplicativeMaybe_c
                        ]
                      )
                      (termbind
                        (strict)
                        (vardecl
                          fromData
                          (all a (type) (fun [IsData a] (fun Data [Maybe a])))
                        )
                        (abs
                          a
                          (type)
                          (lam
                            v
                            [IsData a]
                            [
                              { [ { IsData_match a } v ] (fun Data [Maybe a]) }
                              (lam v (fun a Data) (lam v (fun Data [Maybe a]) v)
                              )
                            ]
                          )
                        )
                      )
                      (termbind
                        (strict)
                        (vardecl
                          fIsDataTuple2_cfromData
                          (all a (type) (all b (type) (fun [IsData a] (fun [IsData b] (fun Data [Maybe [[Tuple2 a] b]])))))
                        )
                        (abs
                          a
                          (type)
                          (abs
                            b
                            (type)
                            (lam
                              dIsData
                              [IsData a]
                              (lam
                                dIsData
                                [IsData b]
                                (lam
                                  ds
                                  Data
                                  [
                                    [
                                      [
                                        [
                                          [
                                            [
                                              {
                                                [ Data_match ds ]
                                                (fun Unit [Maybe [[Tuple2 a] b]])
                                              }
                                              (lam
                                                default_arg0
                                                (con bytestring)
                                                (lam
                                                  thunk
                                                  Unit
                                                  { Nothing [[Tuple2 a] b] }
                                                )
                                              )
                                            ]
                                            (lam
                                              i
                                              (con integer)
                                              (lam
                                                ds
                                                [List Data]
                                                (lam
                                                  thunk
                                                  Unit
                                                  [
                                                    [
                                                      [
                                                        {
                                                          [
                                                            { Nil_match Data }
                                                            ds
                                                          ]
                                                          (fun Unit [Maybe [[Tuple2 a] b]])
                                                        }
                                                        (lam
                                                          thunk
                                                          Unit
                                                          {
                                                            Nothing
                                                            [[Tuple2 a] b]
                                                          }
                                                        )
                                                      ]
                                                      (lam
                                                        arg
                                                        Data
                                                        (lam
                                                          ds
                                                          [List Data]
                                                          (lam
                                                            thunk
                                                            Unit
                                                            [
                                                              [
                                                                [
                                                                  {
                                                                    [
                                                                      {
                                                                        Nil_match
                                                                        Data
                                                                      }
                                                                      ds
                                                                    ]
                                                                    (fun Unit [Maybe [[Tuple2 a] b]])
                                                                  }
                                                                  (lam
                                                                    thunk
                                                                    Unit
                                                                    {
                                                                      Nothing
                                                                      [[Tuple2 a] b]
                                                                    }
                                                                  )
                                                                ]
                                                                (lam
                                                                  arg
                                                                  Data
                                                                  (lam
                                                                    ds
                                                                    [List Data]
                                                                    (lam
                                                                      thunk
                                                                      Unit
                                                                      [
                                                                        [
                                                                          [
                                                                            {
                                                                              [
                                                                                {
                                                                                  Nil_match
                                                                                  Data
                                                                                }
                                                                                ds
                                                                              ]
                                                                              (fun Unit [Maybe [[Tuple2 a] b]])
                                                                            }
                                                                            (lam
                                                                              thunk
                                                                              Unit
                                                                              [
                                                                                [
                                                                                  [
                                                                                    {
                                                                                      [
                                                                                        Bool_match
                                                                                        [
                                                                                          [
                                                                                            equalsInteger
                                                                                            i
                                                                                          ]
                                                                                          (con
                                                                                            integer
                                                                                              0
                                                                                          )
                                                                                        ]
                                                                                      ]
                                                                                      (fun Unit [Maybe [[Tuple2 a] b]])
                                                                                    }
                                                                                    (lam
                                                                                      thunk
                                                                                      Unit
                                                                                      [
                                                                                        [
                                                                                          [
                                                                                            {
                                                                                              [
                                                                                                {
                                                                                                  Maybe_match
                                                                                                  a
                                                                                                }
                                                                                                [
                                                                                                  [
                                                                                                    {
                                                                                                      fromData
                                                                                                      a
                                                                                                    }
                                                                                                    dIsData
                                                                                                  ]
                                                                                                  arg
                                                                                                ]
                                                                                              ]
                                                                                              (fun Unit [Maybe [[Tuple2 a] b]])
                                                                                            }
                                                                                            (lam
                                                                                              ipv
                                                                                              a
                                                                                              (lam
                                                                                                thunk
                                                                                                Unit
                                                                                                [
                                                                                                  [
                                                                                                    [
                                                                                                      {
                                                                                                        [
                                                                                                          {
                                                                                                            Maybe_match
                                                                                                            b
                                                                                                          }
                                                                                                          [
                                                                                                            [
                                                                                                              {
                                                                                                                fromData
                                                                                                                b
                                                                                                              }
                                                                                                              dIsData
                                                                                                            ]
                                                                                                            arg
                                                                                                          ]
                                                                                                        ]
                                                                                                        (fun Unit [Maybe [[Tuple2 a] b]])
                                                                                                      }
                                                                                                      (lam
                                                                                                        ipv
                                                                                                        b
                                                                                                        (lam
                                                                                                          thunk
                                                                                                          Unit
                                                                                                          [
                                                                                                            {
                                                                                                              Just
                                                                                                              [[Tuple2 a] b]
                                                                                                            }
                                                                                                            [
                                                                                                              [
                                                                                                                {
                                                                                                                  {
                                                                                                                    Tuple2
                                                                                                                    a
                                                                                                                  }
                                                                                                                  b
                                                                                                                }
                                                                                                                ipv
                                                                                                              ]
                                                                                                              ipv
                                                                                                            ]
                                                                                                          ]
                                                                                                        )
                                                                                                      )
                                                                                                    ]
                                                                                                    (lam
                                                                                                      thunk
                                                                                                      Unit
                                                                                                      {
                                                                                                        Nothing
                                                                                                        [[Tuple2 a] b]
                                                                                                      }
                                                                                                    )
                                                                                                  ]
                                                                                                  Unit
                                                                                                ]
                                                                                              )
                                                                                            )
                                                                                          ]
                                                                                          (lam
                                                                                            thunk
                                                                                            Unit
                                                                                            {
                                                                                              Nothing
                                                                                              [[Tuple2 a] b]
                                                                                            }
                                                                                          )
                                                                                        ]
                                                                                        Unit
                                                                                      ]
                                                                                    )
                                                                                  ]
                                                                                  (lam
                                                                                    thunk
                                                                                    Unit
                                                                                    {
                                                                                      Nothing
                                                                                      [[Tuple2 a] b]
                                                                                    }
                                                                                  )
                                                                                ]
                                                                                Unit
                                                                              ]
                                                                            )
                                                                          ]
                                                                          (lam
                                                                            ipv
                                                                            Data
                                                                            (lam
                                                                              ipv
                                                                              [List Data]
                                                                              (lam
                                                                                thunk
                                                                                Unit
                                                                                {
                                                                                  Nothing
                                                                                  [[Tuple2 a] b]
                                                                                }
                                                                              )
                                                                            )
                                                                          )
                                                                        ]
                                                                        Unit
                                                                      ]
                                                                    )
                                                                  )
                                                                )
                                                              ]
                                                              Unit
                                                            ]
                                                          )
                                                        )
                                                      )
                                                    ]
                                                    Unit
                                                  ]
                                                )
                                              )
                                            )
                                          ]
                                          (lam
                                            default_arg0
                                            (con integer)
                                            (lam
                                              thunk
                                              Unit
                                              { Nothing [[Tuple2 a] b] }
                                            )
                                          )
                                        ]
                                        (lam
                                          default_arg0
                                          [List Data]
                                          (lam
                                            thunk
                                            Unit
                                            { Nothing [[Tuple2 a] b] }
                                          )
                                        )
                                      ]
                                      (lam
                                        default_arg0
                                        [List [[Tuple2 Data] Data]]
                                        (lam
                                          thunk Unit { Nothing [[Tuple2 a] b] }
                                        )
                                      )
                                    ]
                                    Unit
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
                          p1Applicative
                          (all f (fun (type) (type)) (fun [Applicative f] [(lam f (fun (type) (type)) (all a (type) (all b (type) (fun (fun a b) (fun [f a] [f b]))))) f]))
                        )
                        (abs
                          f
                          (fun (type) (type))
                          (lam
                            v
                            [Applicative f]
                            [
                              {
                                [ { Applicative_match f } v ]
                                [(lam f (fun (type) (type)) (all a (type) (all b (type) (fun (fun a b) (fun [f a] [f b]))))) f]
                              }
                              (lam
                                v
                                [(lam f (fun (type) (type)) (all a (type) (all b (type) (fun (fun a b) (fun [f a] [f b]))))) f]
                                (lam
                                  v
                                  (all a (type) (fun a [f a]))
                                  (lam
                                    v
                                    (all a (type) (all b (type) (fun [f (fun a b)] (fun [f a] [f b]))))
                                    v
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
                          bad_name
                          (all f (fun (type) (type)) (fun [Applicative f] (all a (type) (all b (type) (fun [f (fun a b)] (fun [f a] [f b]))))))
                        )
                        (abs
                          f
                          (fun (type) (type))
                          (lam
                            v
                            [Applicative f]
                            [
                              {
                                [ { Applicative_match f } v ]
                                (all a (type) (all b (type) (fun [f (fun a b)] (fun [f a] [f b]))))
                              }
                              (lam
                                v
                                [(lam f (fun (type) (type)) (all a (type) (all b (type) (fun (fun a b) (fun [f a] [f b]))))) f]
                                (lam
                                  v
                                  (all a (type) (fun a [f a]))
                                  (lam
                                    v
                                    (all a (type) (all b (type) (fun [f (fun a b)] (fun [f a] [f b]))))
                                    v
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
                          pure
                          (all f (fun (type) (type)) (fun [Applicative f] (all a (type) (fun a [f a]))))
                        )
                        (abs
                          f
                          (fun (type) (type))
                          (lam
                            v
                            [Applicative f]
                            [
                              {
                                [ { Applicative_match f } v ]
                                (all a (type) (fun a [f a]))
                              }
                              (lam
                                v
                                [(lam f (fun (type) (type)) (all a (type) (all b (type) (fun (fun a b) (fun [f a] [f b]))))) f]
                                (lam
                                  v
                                  (all a (type) (fun a [f a]))
                                  (lam
                                    v
                                    (all a (type) (all b (type) (fun [f (fun a b)] (fun [f a] [f b]))))
                                    v
                                  )
                                )
                              )
                            ]
                          )
                        )
                      )
                      (let
                        (rec)
                        (termbind
                          (nonstrict)
                          (vardecl
                            fTraversableNil_ctraverse
                            (all f (fun (type) (type)) (all a (type) (all b (type) (fun [Applicative f] (fun (fun a [f b]) (fun [List a] [f [List b]]))))))
                          )
                          (abs
                            f
                            (fun (type) (type))
                            (abs
                              a
                              (type)
                              (abs
                                b
                                (type)
                                (lam
                                  dApplicative
                                  [Applicative f]
                                  (lam
                                    ds
                                    (fun a [f b])
                                    (lam
                                      ds
                                      [List a]
                                      [
                                        [
                                          [
                                            {
                                              [ { Nil_match a } ds ]
                                              (fun Unit [f [List b]])
                                            }
                                            (lam
                                              thunk
                                              Unit
                                              [
                                                {
                                                  [ { pure f } dApplicative ]
                                                  [List b]
                                                }
                                                { Nil b }
                                              ]
                                            )
                                          ]
                                          (lam
                                            x
                                            a
                                            (lam
                                              xs
                                              [List a]
                                              (lam
                                                thunk
                                                Unit
                                                [
                                                  [
                                                    {
                                                      {
                                                        [
                                                          { bad_name f }
                                                          dApplicative
                                                        ]
                                                        [List b]
                                                      }
                                                      [List b]
                                                    }
                                                    [
                                                      [
                                                        {
                                                          {
                                                            [
                                                              {
                                                                p1Applicative f
                                                              }
                                                              dApplicative
                                                            ]
                                                            b
                                                          }
                                                          (fun [List b] [List b])
                                                        }
                                                        { Cons b }
                                                      ]
                                                      [ ds x ]
                                                    ]
                                                  ]
                                                  [
                                                    [
                                                      [
                                                        {
                                                          {
                                                            {
                                                              fTraversableNil_ctraverse
                                                              f
                                                            }
                                                            a
                                                          }
                                                          b
                                                        }
                                                        dApplicative
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
                                        Unit
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
                              fIsDataMap
                              (all k (type) (all v (type) (fun [IsData k] (fun [IsData v] (fun Data [Maybe [List [[Tuple2 k] v]]])))))
                            )
                            (abs
                              k
                              (type)
                              (abs
                                v
                                (type)
                                (lam
                                  dIsData
                                  [IsData k]
                                  (lam
                                    dIsData
                                    [IsData v]
                                    (lam
                                      ds
                                      Data
                                      [
                                        [
                                          [
                                            [
                                              [
                                                [
                                                  {
                                                    [ Data_match ds ]
                                                    (fun Unit [Maybe [List [[Tuple2 k] v]]])
                                                  }
                                                  (lam
                                                    default_arg0
                                                    (con bytestring)
                                                    (lam
                                                      thunk
                                                      Unit
                                                      {
                                                        Nothing
                                                        [List [[Tuple2 k] v]]
                                                      }
                                                    )
                                                  )
                                                ]
                                                (lam
                                                  default_arg0
                                                  (con integer)
                                                  (lam
                                                    default_arg1
                                                    [List Data]
                                                    (lam
                                                      thunk
                                                      Unit
                                                      {
                                                        Nothing
                                                        [List [[Tuple2 k] v]]
                                                      }
                                                    )
                                                  )
                                                )
                                              ]
                                              (lam
                                                default_arg0
                                                (con integer)
                                                (lam
                                                  thunk
                                                  Unit
                                                  {
                                                    Nothing
                                                    [List [[Tuple2 k] v]]
                                                  }
                                                )
                                              )
                                            ]
                                            (lam
                                              ds
                                              [List Data]
                                              (lam
                                                thunk
                                                Unit
                                                [
                                                  [
                                                    [
                                                      {
                                                        {
                                                          {
                                                            fTraversableNil_ctraverse
                                                            Maybe
                                                          }
                                                          Data
                                                        }
                                                        [[Tuple2 k] v]
                                                      }
                                                      fApplicativeMaybe
                                                    ]
                                                    [
                                                      [
                                                        {
                                                          {
                                                            fIsDataTuple2_cfromData
                                                            k
                                                          }
                                                          v
                                                        }
                                                        dIsData
                                                      ]
                                                      dIsData
                                                    ]
                                                  ]
                                                  ds
                                                ]
                                              )
                                            )
                                          ]
                                          (lam
                                            default_arg0
                                            [List [[Tuple2 Data] Data]]
                                            (lam
                                              thunk
                                              Unit
                                              { Nothing [List [[Tuple2 k] v]] }
                                            )
                                          )
                                        ]
                                        Unit
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
                              toData
                              (all a (type) (fun [IsData a] (fun a Data)))
                            )
                            (abs
                              a
                              (type)
                              (lam
                                v
                                [IsData a]
                                [
                                  { [ { IsData_match a } v ] (fun a Data) }
                                  (lam
                                    v
                                    (fun a Data)
                                    (lam v (fun Data [Maybe a]) v)
                                  )
                                ]
                              )
                            )
                          )
                          (termbind
                            (strict)
                            (vardecl
                              fIsDataTuple2_ctoData
                              (all a (type) (all b (type) (fun [IsData a] (fun [IsData b] (fun [[Tuple2 a] b] Data)))))
                            )
                            (abs
                              a
                              (type)
                              (abs
                                b
                                (type)
                                (lam
                                  dIsData
                                  [IsData a]
                                  (lam
                                    dIsData
                                    [IsData b]
                                    (lam
                                      ds
                                      [[Tuple2 a] b]
                                      [
                                        { [ { { Tuple2_match a } b } ds ] Data }
                                        (lam
                                          arg
                                          a
                                          (lam
                                            arg
                                            b
                                            [
                                              [ Constr (con integer 0) ]
                                              [
                                                { build Data }
                                                (abs
                                                  a
                                                  (type)
                                                  (lam
                                                    c
                                                    (fun Data (fun a a))
                                                    (lam
                                                      n
                                                      a
                                                      [
                                                        [
                                                          c
                                                          [
                                                            [
                                                              { toData a }
                                                              dIsData
                                                            ]
                                                            arg
                                                          ]
                                                        ]
                                                        [
                                                          [
                                                            c
                                                            [
                                                              [
                                                                { toData b }
                                                                dIsData
                                                              ]
                                                              arg
                                                            ]
                                                          ]
                                                          n
                                                        ]
                                                      ]
                                                    )
                                                  )
                                                )
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
                            (strict)
                            (vardecl
                              fIsDataMap
                              (all k (type) (all v (type) (fun [IsData k] (fun [IsData v] (fun [List [[Tuple2 k] v]] Data)))))
                            )
                            (abs
                              k
                              (type)
                              (abs
                                v
                                (type)
                                (lam
                                  dIsData
                                  [IsData k]
                                  (lam
                                    dIsData
                                    [IsData v]
                                    (lam
                                      xs
                                      [List [[Tuple2 k] v]]
                                      [
                                        List
                                        [
                                          [
                                            {
                                              {
                                                fFunctorNil_cfmap [[Tuple2 k] v]
                                              }
                                              Data
                                            }
                                            [
                                              [
                                                {
                                                  { fIsDataTuple2_ctoData k } v
                                                }
                                                dIsData
                                              ]
                                              dIsData
                                            ]
                                          ]
                                          xs
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
                              fIsDataMap
                              (all k (type) (all v (type) (fun [IsData k] (fun [IsData v] [IsData [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) k] v]]))))
                            )
                            (abs
                              k
                              (type)
                              (abs
                                v
                                (type)
                                (lam
                                  v
                                  [IsData k]
                                  (lam
                                    v
                                    [IsData v]
                                    [
                                      [
                                        {
                                          CConsIsData
                                          [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) k] v]
                                        }
                                        [ [ { { fIsDataMap k } v } v ] v ]
                                      ]
                                      [ [ { { fIsDataMap k } v } v ] v ]
                                    ]
                                  )
                                )
                              )
                            )
                          )
                          (termbind
                            (nonstrict)
                            (vardecl fIsDataTokenName [IsData (con bytestring)])
                            [
                              [ { CConsIsData (con bytestring) } B ]
                              fIsDataByteString_cfromData
                            ]
                          )
                          (termbind
                            (nonstrict)
                            (vardecl
                              fIsDataValue
                              [IsData [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                            )
                            [
                              [
                                {
                                  { fIsDataMap (con bytestring) } (con integer)
                                }
                                fIsDataTokenName
                              ]
                              fIsDataInteger
                            ]
                          )
                          (termbind
                            (nonstrict)
                            (vardecl
                              fIsDataValue
                              (fun Data [Maybe [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]])
                            )
                            [
                              [
                                {
                                  { fIsDataTuple2_cfromData (con bytestring) }
                                  [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]
                                }
                                fIsDataCurrencySymbol
                              ]
                              fIsDataValue
                            ]
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
                          (termbind
                            (strict)
                            (vardecl
                              sfIsDataObservation_sfIsDataObservation_cfromData
                              (fun Data [Maybe [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]])
                            )
                            (lam
                              ds
                              Data
                              [
                                [
                                  [
                                    [
                                      [
                                        [
                                          {
                                            [ Data_match ds ]
                                            (fun Unit [Maybe [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]])
                                          }
                                          (lam
                                            default_arg0
                                            (con bytestring)
                                            (lam
                                              thunk
                                              Unit
                                              {
                                                Nothing
                                                [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                              }
                                            )
                                          )
                                        ]
                                        (lam
                                          i
                                          (con integer)
                                          (lam
                                            ds
                                            [List Data]
                                            (lam
                                              thunk
                                              Unit
                                              [
                                                [
                                                  [
                                                    {
                                                      [ { Nil_match Data } ds ]
                                                      (fun Unit [Maybe [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]])
                                                    }
                                                    (lam
                                                      thunk
                                                      Unit
                                                      {
                                                        Nothing
                                                        [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                      }
                                                    )
                                                  ]
                                                  (lam
                                                    arg
                                                    Data
                                                    (lam
                                                      ds
                                                      [List Data]
                                                      (lam
                                                        thunk
                                                        Unit
                                                        [
                                                          [
                                                            [
                                                              {
                                                                [
                                                                  {
                                                                    Nil_match
                                                                    Data
                                                                  }
                                                                  ds
                                                                ]
                                                                (fun Unit [Maybe [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]])
                                                              }
                                                              (lam
                                                                thunk
                                                                Unit
                                                                {
                                                                  Nothing
                                                                  [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                                }
                                                              )
                                                            ]
                                                            (lam
                                                              arg
                                                              Data
                                                              (lam
                                                                ds
                                                                [List Data]
                                                                (lam
                                                                  thunk
                                                                  Unit
                                                                  [
                                                                    [
                                                                      [
                                                                        {
                                                                          [
                                                                            {
                                                                              Nil_match
                                                                              Data
                                                                            }
                                                                            ds
                                                                          ]
                                                                          (fun Unit [Maybe [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]])
                                                                        }
                                                                        (lam
                                                                          thunk
                                                                          Unit
                                                                          [
                                                                            [
                                                                              [
                                                                                {
                                                                                  [
                                                                                    Bool_match
                                                                                    [
                                                                                      [
                                                                                        equalsInteger
                                                                                        i
                                                                                      ]
                                                                                      (con
                                                                                        integer
                                                                                          0
                                                                                      )
                                                                                    ]
                                                                                  ]
                                                                                  (fun Unit [Maybe [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]])
                                                                                }
                                                                                (lam
                                                                                  thunk
                                                                                  Unit
                                                                                  [
                                                                                    [
                                                                                      [
                                                                                        [
                                                                                          [
                                                                                            [
                                                                                              {
                                                                                                [
                                                                                                  Data_match
                                                                                                  arg
                                                                                                ]
                                                                                                (fun Unit [Maybe [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]])
                                                                                              }
                                                                                              (lam
                                                                                                default_arg0
                                                                                                (con bytestring)
                                                                                                (lam
                                                                                                  thunk
                                                                                                  Unit
                                                                                                  {
                                                                                                    Nothing
                                                                                                    [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                                                                  }
                                                                                                )
                                                                                              )
                                                                                            ]
                                                                                            (lam
                                                                                              default_arg0
                                                                                              (con integer)
                                                                                              (lam
                                                                                                default_arg1
                                                                                                [List Data]
                                                                                                (lam
                                                                                                  thunk
                                                                                                  Unit
                                                                                                  {
                                                                                                    Nothing
                                                                                                    [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                                                                  }
                                                                                                )
                                                                                              )
                                                                                            )
                                                                                          ]
                                                                                          (lam
                                                                                            default_arg0
                                                                                            (con integer)
                                                                                            (lam
                                                                                              thunk
                                                                                              Unit
                                                                                              {
                                                                                                Nothing
                                                                                                [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                                                              }
                                                                                            )
                                                                                          )
                                                                                        ]
                                                                                        (lam
                                                                                          ds
                                                                                          [List Data]
                                                                                          (lam
                                                                                            thunk
                                                                                            Unit
                                                                                            [
                                                                                              [
                                                                                                [
                                                                                                  {
                                                                                                    [
                                                                                                      {
                                                                                                        Maybe_match
                                                                                                        [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                      }
                                                                                                      [
                                                                                                        [
                                                                                                          [
                                                                                                            {
                                                                                                              {
                                                                                                                {
                                                                                                                  fTraversableNil_ctraverse
                                                                                                                  Maybe
                                                                                                                }
                                                                                                                Data
                                                                                                              }
                                                                                                              [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                            }
                                                                                                            fApplicativeMaybe
                                                                                                          ]
                                                                                                          fIsDataValue
                                                                                                        ]
                                                                                                        ds
                                                                                                      ]
                                                                                                    ]
                                                                                                    (fun Unit [Maybe [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]])
                                                                                                  }
                                                                                                  (lam
                                                                                                    ipv
                                                                                                    [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                    (lam
                                                                                                      thunk
                                                                                                      Unit
                                                                                                      [
                                                                                                        [
                                                                                                          [
                                                                                                            [
                                                                                                              [
                                                                                                                [
                                                                                                                  {
                                                                                                                    [
                                                                                                                      Data_match
                                                                                                                      arg
                                                                                                                    ]
                                                                                                                    (fun Unit [Maybe [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]])
                                                                                                                  }
                                                                                                                  (lam
                                                                                                                    default_arg0
                                                                                                                    (con bytestring)
                                                                                                                    (lam
                                                                                                                      thunk
                                                                                                                      Unit
                                                                                                                      {
                                                                                                                        Nothing
                                                                                                                        [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                                                                                      }
                                                                                                                    )
                                                                                                                  )
                                                                                                                ]
                                                                                                                (lam
                                                                                                                  default_arg0
                                                                                                                  (con integer)
                                                                                                                  (lam
                                                                                                                    default_arg1
                                                                                                                    [List Data]
                                                                                                                    (lam
                                                                                                                      thunk
                                                                                                                      Unit
                                                                                                                      {
                                                                                                                        Nothing
                                                                                                                        [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                                                                                      }
                                                                                                                    )
                                                                                                                  )
                                                                                                                )
                                                                                                              ]
                                                                                                              (lam
                                                                                                                i
                                                                                                                (con integer)
                                                                                                                (lam
                                                                                                                  thunk
                                                                                                                  Unit
                                                                                                                  [
                                                                                                                    {
                                                                                                                      Just
                                                                                                                      [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                                                                                    }
                                                                                                                    [
                                                                                                                      [
                                                                                                                        {
                                                                                                                          Observation
                                                                                                                          [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                        }
                                                                                                                        ipv
                                                                                                                      ]
                                                                                                                      i
                                                                                                                    ]
                                                                                                                  ]
                                                                                                                )
                                                                                                              )
                                                                                                            ]
                                                                                                            (lam
                                                                                                              default_arg0
                                                                                                              [List Data]
                                                                                                              (lam
                                                                                                                thunk
                                                                                                                Unit
                                                                                                                {
                                                                                                                  Nothing
                                                                                                                  [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                                                                                }
                                                                                                              )
                                                                                                            )
                                                                                                          ]
                                                                                                          (lam
                                                                                                            default_arg0
                                                                                                            [List [[Tuple2 Data] Data]]
                                                                                                            (lam
                                                                                                              thunk
                                                                                                              Unit
                                                                                                              {
                                                                                                                Nothing
                                                                                                                [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                                                                              }
                                                                                                            )
                                                                                                          )
                                                                                                        ]
                                                                                                        Unit
                                                                                                      ]
                                                                                                    )
                                                                                                  )
                                                                                                ]
                                                                                                (lam
                                                                                                  thunk
                                                                                                  Unit
                                                                                                  {
                                                                                                    Nothing
                                                                                                    [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                                                                  }
                                                                                                )
                                                                                              ]
                                                                                              Unit
                                                                                            ]
                                                                                          )
                                                                                        )
                                                                                      ]
                                                                                      (lam
                                                                                        default_arg0
                                                                                        [List [[Tuple2 Data] Data]]
                                                                                        (lam
                                                                                          thunk
                                                                                          Unit
                                                                                          {
                                                                                            Nothing
                                                                                            [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                                                          }
                                                                                        )
                                                                                      )
                                                                                    ]
                                                                                    Unit
                                                                                  ]
                                                                                )
                                                                              ]
                                                                              (lam
                                                                                thunk
                                                                                Unit
                                                                                {
                                                                                  Nothing
                                                                                  [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                                                }
                                                                              )
                                                                            ]
                                                                            Unit
                                                                          ]
                                                                        )
                                                                      ]
                                                                      (lam
                                                                        ipv
                                                                        Data
                                                                        (lam
                                                                          ipv
                                                                          [List Data]
                                                                          (lam
                                                                            thunk
                                                                            Unit
                                                                            {
                                                                              Nothing
                                                                              [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                                            }
                                                                          )
                                                                        )
                                                                      )
                                                                    ]
                                                                    Unit
                                                                  ]
                                                                )
                                                              )
                                                            )
                                                          ]
                                                          Unit
                                                        ]
                                                      )
                                                    )
                                                  )
                                                ]
                                                Unit
                                              ]
                                            )
                                          )
                                        )
                                      ]
                                      (lam
                                        default_arg0
                                        (con integer)
                                        (lam
                                          thunk
                                          Unit
                                          {
                                            Nothing
                                            [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                          }
                                        )
                                      )
                                    ]
                                    (lam
                                      default_arg0
                                      [List Data]
                                      (lam
                                        thunk
                                        Unit
                                        {
                                          Nothing
                                          [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                        }
                                      )
                                    )
                                  ]
                                  (lam
                                    default_arg0
                                    [List [[Tuple2 Data] Data]]
                                    (lam
                                      thunk
                                      Unit
                                      {
                                        Nothing
                                        [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                      }
                                    )
                                  )
                                ]
                                Unit
                              ]
                            )
                          )
                          (termbind
                            (strict)
                            (vardecl trace (fun (con string) Unit))
                            (lam
                              arg
                              (con string)
                              [
                                (lam b (con unit) Unit) [ (builtin trace) arg ]
                              ]
                            )
                          )
                          (termbind
                            (nonstrict)
                            (vardecl scheckHashConstraints Unit)
                            [ trace (con string "DecodingError") ]
                          )
                          (datatypebind
                            (datatype
                              (tyvardecl SignedMessage (fun (type) (type)))
                              (tyvardecl a (type))
                              SignedMessage_match
                              (vardecl
                                SignedMessage
                                (fun (con bytestring) (fun (con bytestring) (fun Data [SignedMessage a])))
                              )
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
                                  [
                                    [
                                      [
                                        {
                                          [ Role_match role ] (fun Unit Margins)
                                        }
                                        (lam
                                          thunk
                                          Unit
                                          [
                                            {
                                              [ Margins_match accounts ] Margins
                                            }
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
                                                      [
                                                        unionWith
                                                        (builtin addInteger)
                                                      ]
                                                      ds
                                                    ]
                                                    value
                                                  ]
                                                ]
                                              )
                                            )
                                          ]
                                        )
                                      ]
                                      (lam
                                        thunk
                                        Unit
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
                                                      [
                                                        unionWith
                                                        (builtin addInteger)
                                                      ]
                                                      ds
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
                                    Unit
                                  ]
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
                                      [ { LowerBound a } [ { Finite a } s ] ]
                                      True
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
                              greaterThanInteger
                              (fun (con integer) (fun (con integer) Bool))
                            )
                            (lam
                              arg
                              (con integer)
                              (lam
                                arg
                                (con integer)
                                [
                                  (lam
                                    b
                                    (con bool)
                                    [
                                      [
                                        [ { (builtin ifThenElse) Bool } b ] True
                                      ]
                                      False
                                    ]
                                  )
                                  [ [ (builtin greaterThanInteger) arg ] arg ]
                                ]
                              )
                            )
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
                          (termbind
                            (strict)
                            (vardecl
                              verifySignature
                              (fun (con bytestring) (fun (con bytestring) (fun (con bytestring) Bool)))
                            )
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
                                    (lam
                                      b
                                      (con bool)
                                      [
                                        [
                                          [ { (builtin ifThenElse) Bool } b ]
                                          True
                                        ]
                                        False
                                      ]
                                    )
                                    [
                                      [ [ (builtin verifySignature) arg ] arg ]
                                      arg
                                    ]
                                  ]
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
                                                [
                                                  [
                                                    unionWith
                                                    (builtin addInteger)
                                                  ]
                                                  ds
                                                ]
                                                [
                                                  [
                                                    fAdditiveGroupValue_cscale
                                                    ds
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
                                        [
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
                                                (fun Unit Bool)
                                              }
                                              (lam thunk Unit True)
                                            ]
                                            (lam
                                              ds
                                              [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]]
                                              (lam
                                                xs
                                                [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]]]
                                                (lam
                                                  thunk
                                                  Unit
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
                                                              [
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
                                                                      (fun Unit Bool)
                                                                    }
                                                                    (lam
                                                                      thunk
                                                                      Unit
                                                                      [ go xs ]
                                                                    )
                                                                  ]
                                                                  (lam
                                                                    ds
                                                                    [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]
                                                                    (lam
                                                                      xs
                                                                      [List [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]]
                                                                      (lam
                                                                        thunk
                                                                        Unit
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
                                                                                      [
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
                                                                                              (fun Unit Bool)
                                                                                            }
                                                                                            (lam
                                                                                              thunk
                                                                                              Unit
                                                                                              [
                                                                                                go
                                                                                                xs
                                                                                              ]
                                                                                            )
                                                                                          ]
                                                                                          (lam
                                                                                            thunk
                                                                                            Unit
                                                                                            False
                                                                                          )
                                                                                        ]
                                                                                        Unit
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
                                                                                              (fun Unit Bool)
                                                                                            }
                                                                                            (lam
                                                                                              thunk
                                                                                              Unit
                                                                                              [
                                                                                                go
                                                                                                xs
                                                                                              ]
                                                                                            )
                                                                                          ]
                                                                                          (lam
                                                                                            thunk
                                                                                            Unit
                                                                                            False
                                                                                          )
                                                                                        ]
                                                                                        Unit
                                                                                      ]
                                                                                    )
                                                                                  )
                                                                                ]
                                                                                (lam
                                                                                  a
                                                                                  (con integer)
                                                                                  [
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
                                                                                          (fun Unit Bool)
                                                                                        }
                                                                                        (lam
                                                                                          thunk
                                                                                          Unit
                                                                                          [
                                                                                            go
                                                                                            xs
                                                                                          ]
                                                                                        )
                                                                                      ]
                                                                                      (lam
                                                                                        thunk
                                                                                        Unit
                                                                                        False
                                                                                      )
                                                                                    ]
                                                                                    Unit
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
                                                                Unit
                                                              ]
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
                                          Unit
                                        ]
                                      )
                                    )
                                    [ go [ [ unionVal l ] r ] ]
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
                                    [
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
                                            (fun Unit Bool)
                                          }
                                          (lam thunk Unit True)
                                        ]
                                        (lam
                                          ds
                                          [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                          (lam
                                            xs
                                            [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                            (lam
                                              thunk
                                              Unit
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
                                                          [
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
                                                                  (fun Unit Bool)
                                                                }
                                                                (lam
                                                                  thunk
                                                                  Unit
                                                                  [ go xs ]
                                                                )
                                                              ]
                                                              (lam
                                                                ds
                                                                [[Tuple2 (con bytestring)] (con integer)]
                                                                (lam
                                                                  xs
                                                                  [List [[Tuple2 (con bytestring)] (con integer)]]
                                                                  (lam
                                                                    thunk
                                                                    Unit
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
                                                                          [
                                                                            [
                                                                              [
                                                                                {
                                                                                  [
                                                                                    Bool_match
                                                                                    [
                                                                                      [
                                                                                        equalsInteger
                                                                                        (con
                                                                                          integer
                                                                                            0
                                                                                        )
                                                                                      ]
                                                                                      x
                                                                                    ]
                                                                                  ]
                                                                                  (fun Unit Bool)
                                                                                }
                                                                                (lam
                                                                                  thunk
                                                                                  Unit
                                                                                  [
                                                                                    go
                                                                                    xs
                                                                                  ]
                                                                                )
                                                                              ]
                                                                              (lam
                                                                                thunk
                                                                                Unit
                                                                                False
                                                                              )
                                                                            ]
                                                                            Unit
                                                                          ]
                                                                        )
                                                                      )
                                                                    ]
                                                                  )
                                                                )
                                                              )
                                                            ]
                                                            Unit
                                                          ]
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
                                      Unit
                                    ]
                                  )
                                )
                                [ go ds ]
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
                              arg
                              (con integer)
                              (lam
                                arg
                                (con integer)
                                [
                                  (lam
                                    b
                                    (con bool)
                                    [
                                      [
                                        [ { (builtin ifThenElse) Bool } b ] True
                                      ]
                                      False
                                    ]
                                  )
                                  [ [ (builtin lessThanInteger) arg ] arg ]
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
                                [
                                  [
                                    [
                                      {
                                        [ Bool_match [ isZero l ] ]
                                        (fun Unit Bool)
                                      }
                                      (lam
                                        thunk
                                        Unit
                                        [
                                          [
                                            [
                                              {
                                                [ Bool_match [ isZero r ] ]
                                                (fun Unit Bool)
                                              }
                                              (lam thunk Unit False)
                                            ]
                                            (lam
                                              thunk
                                              Unit
                                              [
                                                [
                                                  [
                                                    checkBinRel lessThanInteger
                                                  ]
                                                  l
                                                ]
                                                r
                                              ]
                                            )
                                          ]
                                          Unit
                                        ]
                                      )
                                    ]
                                    (lam
                                      thunk
                                      Unit
                                      [
                                        [ [ checkBinRel lessThanInteger ] l ] r
                                      ]
                                    )
                                  ]
                                  Unit
                                ]
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
                                    [
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
                                            (fun Unit [Maybe Role])
                                          }
                                          (lam
                                            thunk Unit [ { Just Role } Short ]
                                          )
                                        ]
                                        (lam
                                          thunk
                                          Unit
                                          [
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
                                                  (fun Unit [Maybe Role])
                                                }
                                                (lam
                                                  thunk
                                                  Unit
                                                  [ { Just Role } Long ]
                                                )
                                              ]
                                              (lam thunk Unit { Nothing Role })
                                            ]
                                            Unit
                                          ]
                                        )
                                      ]
                                      Unit
                                    ]
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
                                                          State_match
                                                          FutureState
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
                                                        [
                                                          [
                                                            [
                                                              {
                                                                [
                                                                  FutureState_match
                                                                  ds
                                                                ]
                                                                (fun Unit [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]])
                                                              }
                                                              (lam
                                                                thunk
                                                                Unit
                                                                {
                                                                  Nothing
                                                                  [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]
                                                                }
                                                              )
                                                            ]
                                                            (lam
                                                              accounts
                                                              Margins
                                                              (lam
                                                                thunk
                                                                Unit
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
                                                                                      (builtin
                                                                                        addInteger
                                                                                      )
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
                                                                        {
                                                                          [
                                                                            {
                                                                              SignedMessage_match
                                                                              [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                                            }
                                                                            ov
                                                                          ]
                                                                          [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]]
                                                                        }
                                                                        (lam
                                                                          ds
                                                                          (con bytestring)
                                                                          (lam
                                                                            ds
                                                                            (con bytestring)
                                                                            (lam
                                                                              ds
                                                                              Data
                                                                              [
                                                                                [
                                                                                  [
                                                                                    {
                                                                                      [
                                                                                        Bool_match
                                                                                        [
                                                                                          [
                                                                                            [
                                                                                              verifySignature
                                                                                              ds
                                                                                            ]
                                                                                            ds
                                                                                          ]
                                                                                          ds
                                                                                        ]
                                                                                      ]
                                                                                      (fun Unit [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]])
                                                                                    }
                                                                                    (lam
                                                                                      thunk
                                                                                      Unit
                                                                                      [
                                                                                        [
                                                                                          [
                                                                                            {
                                                                                              [
                                                                                                {
                                                                                                  Maybe_match
                                                                                                  [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                                                                }
                                                                                                [
                                                                                                  sfIsDataObservation_sfIsDataObservation_cfromData
                                                                                                  ds
                                                                                                ]
                                                                                              ]
                                                                                              (fun Unit [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]])
                                                                                            }
                                                                                            (lam
                                                                                              a
                                                                                              [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                                                              (lam
                                                                                                thunk
                                                                                                Unit
                                                                                                [
                                                                                                  {
                                                                                                    [
                                                                                                      {
                                                                                                        Observation_match
                                                                                                        [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                      }
                                                                                                      a
                                                                                                    ]
                                                                                                    [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]]
                                                                                                  }
                                                                                                  (lam
                                                                                                    ds
                                                                                                    [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                    (lam
                                                                                                      ds
                                                                                                      (con integer)
                                                                                                      [
                                                                                                        [
                                                                                                          [
                                                                                                            {
                                                                                                              [
                                                                                                                Bool_match
                                                                                                                [
                                                                                                                  [
                                                                                                                    equalsInteger
                                                                                                                    ds
                                                                                                                  ]
                                                                                                                  ds
                                                                                                                ]
                                                                                                              ]
                                                                                                              (fun Unit [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]])
                                                                                                            }
                                                                                                            (lam
                                                                                                              thunk
                                                                                                              Unit
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
                                                                                                                                                [
                                                                                                                                                  MustHashDatum
                                                                                                                                                  ds
                                                                                                                                                ]
                                                                                                                                                ds
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
                                                                                                          (lam
                                                                                                            thunk
                                                                                                            Unit
                                                                                                            {
                                                                                                              Nothing
                                                                                                              [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]
                                                                                                            }
                                                                                                          )
                                                                                                        ]
                                                                                                        Unit
                                                                                                      ]
                                                                                                    )
                                                                                                  )
                                                                                                ]
                                                                                              )
                                                                                            )
                                                                                          ]
                                                                                          (lam
                                                                                            thunk
                                                                                            Unit
                                                                                            [
                                                                                              [
                                                                                                {
                                                                                                  [
                                                                                                    Unit_match
                                                                                                    scheckHashConstraints
                                                                                                  ]
                                                                                                  (fun Unit [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]])
                                                                                                }
                                                                                                (lam
                                                                                                  thunk
                                                                                                  Unit
                                                                                                  {
                                                                                                    Nothing
                                                                                                    [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]
                                                                                                  }
                                                                                                )
                                                                                              ]
                                                                                              Unit
                                                                                            ]
                                                                                          )
                                                                                        ]
                                                                                        Unit
                                                                                      ]
                                                                                    )
                                                                                  ]
                                                                                  (lam
                                                                                    thunk
                                                                                    Unit
                                                                                    {
                                                                                      Nothing
                                                                                      [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]
                                                                                    }
                                                                                  )
                                                                                ]
                                                                                Unit
                                                                              ]
                                                                            )
                                                                          )
                                                                        )
                                                                      ]
                                                                    )
                                                                  ]
                                                                  (lam
                                                                    ov
                                                                    [SignedMessage [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]]
                                                                    [
                                                                      {
                                                                        [
                                                                          {
                                                                            SignedMessage_match
                                                                            [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                                          }
                                                                          ov
                                                                        ]
                                                                        [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]]
                                                                      }
                                                                      (lam
                                                                        ds
                                                                        (con bytestring)
                                                                        (lam
                                                                          ds
                                                                          (con bytestring)
                                                                          (lam
                                                                            ds
                                                                            Data
                                                                            [
                                                                              [
                                                                                [
                                                                                  {
                                                                                    [
                                                                                      Bool_match
                                                                                      [
                                                                                        [
                                                                                          [
                                                                                            verifySignature
                                                                                            ds
                                                                                          ]
                                                                                          ds
                                                                                        ]
                                                                                        ds
                                                                                      ]
                                                                                    ]
                                                                                    (fun Unit [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]])
                                                                                  }
                                                                                  (lam
                                                                                    thunk
                                                                                    Unit
                                                                                    [
                                                                                      [
                                                                                        [
                                                                                          {
                                                                                            [
                                                                                              {
                                                                                                Maybe_match
                                                                                                [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                                                              }
                                                                                              [
                                                                                                sfIsDataObservation_sfIsDataObservation_cfromData
                                                                                                ds
                                                                                              ]
                                                                                            ]
                                                                                            (fun Unit [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]])
                                                                                          }
                                                                                          (lam
                                                                                            a
                                                                                            [Observation [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                                                            (lam
                                                                                              thunk
                                                                                              Unit
                                                                                              [
                                                                                                {
                                                                                                  [
                                                                                                    {
                                                                                                      Observation_match
                                                                                                      [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                    }
                                                                                                    a
                                                                                                  ]
                                                                                                  [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]]
                                                                                                }
                                                                                                (lam
                                                                                                  ds
                                                                                                  [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                  (lam
                                                                                                    ds
                                                                                                    (con integer)
                                                                                                    [
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
                                                                                                            (fun Unit [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]])
                                                                                                          }
                                                                                                          (lam
                                                                                                            vRole
                                                                                                            Role
                                                                                                            (lam
                                                                                                              thunk
                                                                                                              Unit
                                                                                                              [
                                                                                                                [
                                                                                                                  [
                                                                                                                    {
                                                                                                                      [
                                                                                                                        Bool_match
                                                                                                                        [
                                                                                                                          [
                                                                                                                            greaterThanInteger
                                                                                                                            ds
                                                                                                                          ]
                                                                                                                          ds
                                                                                                                        ]
                                                                                                                      ]
                                                                                                                      (fun Unit [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]])
                                                                                                                    }
                                                                                                                    (lam
                                                                                                                      thunk
                                                                                                                      Unit
                                                                                                                      (let
                                                                                                                        (nonrec
                                                                                                                        )
                                                                                                                        (termbind
                                                                                                                          (nonstrict
                                                                                                                          )
                                                                                                                          (vardecl
                                                                                                                            l
                                                                                                                            [[TxConstraints Void] Void]
                                                                                                                          )
                                                                                                                          [
                                                                                                                            [
                                                                                                                              [
                                                                                                                                {
                                                                                                                                  [
                                                                                                                                    Role_match
                                                                                                                                    vRole
                                                                                                                                  ]
                                                                                                                                  (fun Unit [[TxConstraints Void] Void])
                                                                                                                                }
                                                                                                                                (lam
                                                                                                                                  thunk
                                                                                                                                  Unit
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
                                                                                                                              (lam
                                                                                                                                thunk
                                                                                                                                Unit
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
                                                                                                                            Unit
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
                                                                                                                                      {
                                                                                                                                        [
                                                                                                                                          {
                                                                                                                                            {
                                                                                                                                              TxConstraints_match
                                                                                                                                              Void
                                                                                                                                            }
                                                                                                                                            Void
                                                                                                                                          }
                                                                                                                                          l
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
                                                                                                                                                                MustHashDatum
                                                                                                                                                                ds
                                                                                                                                                              ]
                                                                                                                                                              ds
                                                                                                                                                            ]
                                                                                                                                                          ]
                                                                                                                                                          n
                                                                                                                                                        ]
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
                                                                                                                                      [
                                                                                                                                        {
                                                                                                                                          {
                                                                                                                                            TxConstraints_match
                                                                                                                                            Void
                                                                                                                                          }
                                                                                                                                          Void
                                                                                                                                        }
                                                                                                                                        l
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
                                                                                                                                            ds
                                                                                                                                          ]
                                                                                                                                        )
                                                                                                                                      )
                                                                                                                                    )
                                                                                                                                  ]
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
                                                                                                                                      l
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
                                                                                                                                          ds
                                                                                                                                        ]
                                                                                                                                      )
                                                                                                                                    )
                                                                                                                                  )
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
                                                                                                                  (lam
                                                                                                                    thunk
                                                                                                                    Unit
                                                                                                                    {
                                                                                                                      Nothing
                                                                                                                      [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]
                                                                                                                    }
                                                                                                                  )
                                                                                                                ]
                                                                                                                Unit
                                                                                                              ]
                                                                                                            )
                                                                                                          )
                                                                                                        ]
                                                                                                        (lam
                                                                                                          thunk
                                                                                                          Unit
                                                                                                          {
                                                                                                            Nothing
                                                                                                            [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]
                                                                                                          }
                                                                                                        )
                                                                                                      ]
                                                                                                      Unit
                                                                                                    ]
                                                                                                  )
                                                                                                )
                                                                                              ]
                                                                                            )
                                                                                          )
                                                                                        ]
                                                                                        (lam
                                                                                          thunk
                                                                                          Unit
                                                                                          [
                                                                                            [
                                                                                              {
                                                                                                [
                                                                                                  Unit_match
                                                                                                  scheckHashConstraints
                                                                                                ]
                                                                                                (fun Unit [Maybe [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]])
                                                                                              }
                                                                                              (lam
                                                                                                thunk
                                                                                                Unit
                                                                                                {
                                                                                                  Nothing
                                                                                                  [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]
                                                                                                }
                                                                                              )
                                                                                            ]
                                                                                            Unit
                                                                                          ]
                                                                                        )
                                                                                      ]
                                                                                      Unit
                                                                                    ]
                                                                                  )
                                                                                ]
                                                                                (lam
                                                                                  thunk
                                                                                  Unit
                                                                                  {
                                                                                    Nothing
                                                                                    [[Tuple2 [[TxConstraints Void] Void]] [State FutureState]]
                                                                                  }
                                                                                )
                                                                              ]
                                                                              Unit
                                                                            ]
                                                                          )
                                                                        )
                                                                      )
                                                                    ]
                                                                  )
                                                                ]
                                                              )
                                                            )
                                                          ]
                                                          Unit
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
                                      {
                                        { StateMachine FutureState }
                                        FutureAction
                                      }
                                      [ [ transition ft ] fos ]
                                    ]
                                    (lam
                                      ds
                                      FutureState
                                      [
                                        [
                                          [
                                            {
                                              [ FutureState_match ds ]
                                              (fun Unit Bool)
                                            }
                                            (lam thunk Unit True)
                                          ]
                                          (lam
                                            ipv Margins (lam thunk Unit False)
                                          )
                                        ]
                                        Unit
                                      ]
                                    )
                                  ]
                                  {
                                    { mkStateMachine FutureState } FutureAction
                                  }
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
)