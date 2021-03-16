(program
  (let
    (nonrec)
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
          (datatype (tyvardecl Unit (type))  Unit_match (vardecl Unit Unit))
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
            (tyvardecl CampaignAction (type))

            CampaignAction_match
            (vardecl Collect CampaignAction) (vardecl Refund CampaignAction)
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
                (vardecl LowerBound (fun [Extended a] (fun Bool [LowerBound a]))
                )
              )
            )
            (datatypebind
              (datatype
                (tyvardecl UpperBound (fun (type) (type)))
                (tyvardecl a (type))
                UpperBound_match
                (vardecl UpperBound (fun [Extended a] (fun Bool [UpperBound a]))
                )
              )
            )
            (datatypebind
              (datatype
                (tyvardecl Interval (fun (type) (type)))
                (tyvardecl a (type))
                Interval_match
                (vardecl
                  Interval
                  (fun [LowerBound a] (fun [UpperBound a] [Interval a]))
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
                (tyvardecl Maybe (fun (type) (type)))
                (tyvardecl a (type))
                Maybe_match
                (vardecl Just (fun a [Maybe a])) (vardecl Nothing [Maybe a])
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
                              { [ { Nil_match a } l ] (fun Unit [List b]) }
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
                                    [ [ { { fFunctorNil_cfmap a } b } f ] xs ]
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
                        (lam v [(lam a (type) (fun a (fun a a))) a] (lam v a v))
                      ]
                    )
                  )
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
                            (lam
                              v [(lam a (type) (fun a (fun a a))) a] (lam v a v)
                            )
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
                            (lam
                              v [(lam a (type) (fun a (fun a a))) a] (lam v a v)
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
                                    dSemigroup
                                    [(lam a (type) (fun a (fun a a))) m]
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
                                          {
                                            [ { Nil_match a } ds ] (fun Unit m)
                                          }
                                          (lam
                                            thunk Unit [ { mempty m } dMonoid ]
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
                                                [ dSemigroup [ ds x ] ]
                                                [
                                                  [
                                                    [
                                                      {
                                                        {
                                                          fFoldableNil_cfoldMap
                                                          m
                                                        }
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
                                                                    thunk
                                                                    Unit
                                                                    xs
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
                                  [
                                    [ [ { (builtin ifThenElse) Bool } b ] True ]
                                    False
                                  ]
                                )
                                [ [ (builtin equalsByteString) arg ] arg ]
                              ]
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
                          (nonstrict)
                          (vardecl
                            fMonoidValue_c
                            (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]))
                          )
                          [ unionWith (builtin addInteger) ]
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
                            greaterThanEqInteger
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
                                    [ [ { (builtin ifThenElse) Bool } b ] True ]
                                    False
                                  ]
                                )
                                [
                                  [ (builtin greaterThanEqualsInteger) arg ] arg
                                ]
                              ]
                            )
                          )
                        )
                        (termbind
                          (strict)
                          (vardecl
                            txInInfoValue
                            (fun TxInInfo [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]])
                          )
                          (lam
                            ds
                            TxInInfo
                            [
                              {
                                [ TxInInfo_match ds ]
                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                              }
                              (lam
                                ds
                                TxOutRef
                                (lam
                                  ds
                                  [Maybe [[[Tuple3 (con bytestring)] (con bytestring)] (con bytestring)]]
                                  (lam
                                    ds
                                    [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                    ds
                                  )
                                )
                              )
                            ]
                          )
                        )
                        (termbind
                          (strict)
                          (vardecl
                            equalsInteger
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
                                    [ [ { (builtin ifThenElse) Bool } b ] True ]
                                    False
                                  ]
                                )
                                [ [ (builtin equalsInteger) arg ] arg ]
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
                                    [ [ { (builtin ifThenElse) Bool } b ] True ]
                                    False
                                  ]
                                )
                                [ [ (builtin lessThanEqualsInteger) arg ] arg ]
                              ]
                            )
                          )
                        )
                        (termbind
                          (strict)
                          (vardecl
                            wsfOrdUpperBound0_c
                            (fun [Extended (con integer)] (fun Bool (fun [Extended (con integer)] (fun Bool Bool))))
                          )
                          (lam
                            ww
                            [Extended (con integer)]
                            (lam
                              ww
                              Bool
                              (lam
                                ww
                                [Extended (con integer)]
                                (lam
                                  ww
                                  Bool
                                  [
                                    [
                                      [
                                        [
                                          {
                                            [
                                              { Extended_match (con integer) }
                                              ww
                                            ]
                                            (fun Unit Bool)
                                          }
                                          (lam
                                            default_arg0
                                            (con integer)
                                            (lam
                                              thunk
                                              Unit
                                              [
                                                [
                                                  [
                                                    [
                                                      {
                                                        [
                                                          {
                                                            Extended_match
                                                            (con integer)
                                                          }
                                                          ww
                                                        ]
                                                        (fun Unit Bool)
                                                      }
                                                      (lam
                                                        default_arg0
                                                        (con integer)
                                                        (lam
                                                          thunk
                                                          Unit
                                                          [
                                                            [
                                                              [
                                                                [
                                                                  {
                                                                    [
                                                                      {
                                                                        Extended_match
                                                                        (con integer)
                                                                      }
                                                                      ww
                                                                    ]
                                                                    (fun Unit Bool)
                                                                  }
                                                                  (lam
                                                                    ipv
                                                                    (con integer)
                                                                    (lam
                                                                      thunk
                                                                      Unit
                                                                      [
                                                                        [
                                                                          [
                                                                            [
                                                                              {
                                                                                [
                                                                                  {
                                                                                    Extended_match
                                                                                    (con integer)
                                                                                  }
                                                                                  ww
                                                                                ]
                                                                                (fun Unit Bool)
                                                                              }
                                                                              (lam
                                                                                ipv
                                                                                (con integer)
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
                                                                                                ipv
                                                                                              ]
                                                                                              ipv
                                                                                            ]
                                                                                          ]
                                                                                          (fun Unit Bool)
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
                                                                                                    ww
                                                                                                  ]
                                                                                                  (fun Unit Bool)
                                                                                                }
                                                                                                (lam
                                                                                                  thunk
                                                                                                  Unit
                                                                                                  ww
                                                                                                )
                                                                                              ]
                                                                                              (lam
                                                                                                thunk
                                                                                                Unit
                                                                                                True
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
                                                                                          [
                                                                                            lessThanEqInteger
                                                                                            ipv
                                                                                          ]
                                                                                          ipv
                                                                                        ]
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
                                                                                (abs
                                                                                  e
                                                                                  (type)
                                                                                  (error
                                                                                    e
                                                                                  )
                                                                                )
                                                                                Bool
                                                                              }
                                                                            )
                                                                          ]
                                                                          (lam
                                                                            thunk
                                                                            Unit
                                                                            True
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
                                                                    (abs
                                                                      e
                                                                      (type)
                                                                      (error e)
                                                                    )
                                                                    Bool
                                                                  }
                                                                )
                                                              ]
                                                              (lam
                                                                thunk
                                                                Unit
                                                                [
                                                                  [
                                                                    [
                                                                      [
                                                                        {
                                                                          [
                                                                            {
                                                                              Extended_match
                                                                              (con integer)
                                                                            }
                                                                            ww
                                                                          ]
                                                                          (fun Unit Bool)
                                                                        }
                                                                        (lam
                                                                          ipv
                                                                          (con integer)
                                                                          (lam
                                                                            thunk
                                                                            Unit
                                                                            False
                                                                          )
                                                                        )
                                                                      ]
                                                                      (lam
                                                                        thunk
                                                                        Unit
                                                                        {
                                                                          (abs
                                                                            e
                                                                            (type)
                                                                            (error
                                                                              e
                                                                            )
                                                                          )
                                                                          Bool
                                                                        }
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
                                                                                ww
                                                                              ]
                                                                              (fun Unit Bool)
                                                                            }
                                                                            (lam
                                                                              thunk
                                                                              Unit
                                                                              ww
                                                                            )
                                                                          ]
                                                                          (lam
                                                                            thunk
                                                                            Unit
                                                                            True
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
                                                            Unit
                                                          ]
                                                        )
                                                      )
                                                    ]
                                                    (lam thunk Unit False)
                                                  ]
                                                  (lam
                                                    thunk
                                                    Unit
                                                    [
                                                      [
                                                        [
                                                          [
                                                            {
                                                              [
                                                                {
                                                                  Extended_match
                                                                  (con integer)
                                                                }
                                                                ww
                                                              ]
                                                              (fun Unit Bool)
                                                            }
                                                            (lam
                                                              ipv
                                                              (con integer)
                                                              (lam
                                                                thunk
                                                                Unit
                                                                [
                                                                  [
                                                                    [
                                                                      [
                                                                        {
                                                                          [
                                                                            {
                                                                              Extended_match
                                                                              (con integer)
                                                                            }
                                                                            ww
                                                                          ]
                                                                          (fun Unit Bool)
                                                                        }
                                                                        (lam
                                                                          ipv
                                                                          (con integer)
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
                                                                                          ipv
                                                                                        ]
                                                                                        ipv
                                                                                      ]
                                                                                    ]
                                                                                    (fun Unit Bool)
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
                                                                                              ww
                                                                                            ]
                                                                                            (fun Unit Bool)
                                                                                          }
                                                                                          (lam
                                                                                            thunk
                                                                                            Unit
                                                                                            ww
                                                                                          )
                                                                                        ]
                                                                                        (lam
                                                                                          thunk
                                                                                          Unit
                                                                                          True
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
                                                                                    [
                                                                                      lessThanEqInteger
                                                                                      ipv
                                                                                    ]
                                                                                    ipv
                                                                                  ]
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
                                                                          (abs
                                                                            e
                                                                            (type)
                                                                            (error
                                                                              e
                                                                            )
                                                                          )
                                                                          Bool
                                                                        }
                                                                      )
                                                                    ]
                                                                    (lam
                                                                      thunk
                                                                      Unit
                                                                      True
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
                                                              (abs
                                                                e
                                                                (type)
                                                                (error e)
                                                              )
                                                              Bool
                                                            }
                                                          )
                                                        ]
                                                        (lam
                                                          thunk
                                                          Unit
                                                          [
                                                            [
                                                              [
                                                                [
                                                                  {
                                                                    [
                                                                      {
                                                                        Extended_match
                                                                        (con integer)
                                                                      }
                                                                      ww
                                                                    ]
                                                                    (fun Unit Bool)
                                                                  }
                                                                  (lam
                                                                    ipv
                                                                    (con integer)
                                                                    (lam
                                                                      thunk
                                                                      Unit
                                                                      False
                                                                    )
                                                                  )
                                                                ]
                                                                (lam
                                                                  thunk
                                                                  Unit
                                                                  {
                                                                    (abs
                                                                      e
                                                                      (type)
                                                                      (error e)
                                                                    )
                                                                    Bool
                                                                  }
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
                                                                          ww
                                                                        ]
                                                                        (fun Unit Bool)
                                                                      }
                                                                      (lam
                                                                        thunk
                                                                        Unit
                                                                        ww
                                                                      )
                                                                    ]
                                                                    (lam
                                                                      thunk
                                                                      Unit
                                                                      True
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
                                                      Unit
                                                    ]
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
                                          [
                                            [
                                              [
                                                [
                                                  {
                                                    [
                                                      {
                                                        Extended_match
                                                        (con integer)
                                                      }
                                                      ww
                                                    ]
                                                    (fun Unit Bool)
                                                  }
                                                  (lam
                                                    default_arg0
                                                    (con integer)
                                                    (lam thunk Unit True)
                                                  )
                                                ]
                                                (lam
                                                  thunk
                                                  Unit
                                                  [
                                                    [
                                                      [
                                                        {
                                                          [ Bool_match ww ]
                                                          (fun Unit Bool)
                                                        }
                                                        (lam thunk Unit ww)
                                                      ]
                                                      (lam thunk Unit True)
                                                    ]
                                                    Unit
                                                  ]
                                                )
                                              ]
                                              (lam thunk Unit True)
                                            ]
                                            Unit
                                          ]
                                        )
                                      ]
                                      (lam
                                        thunk
                                        Unit
                                        [
                                          [
                                            [
                                              [
                                                {
                                                  [
                                                    {
                                                      Extended_match
                                                      (con integer)
                                                    }
                                                    ww
                                                  ]
                                                  (fun Unit Bool)
                                                }
                                                (lam
                                                  default_arg0
                                                  (con integer)
                                                  (lam
                                                    thunk
                                                    Unit
                                                    [
                                                      [
                                                        [
                                                          [
                                                            {
                                                              [
                                                                {
                                                                  Extended_match
                                                                  (con integer)
                                                                }
                                                                ww
                                                              ]
                                                              (fun Unit Bool)
                                                            }
                                                            (lam
                                                              ipv
                                                              (con integer)
                                                              (lam
                                                                thunk
                                                                Unit
                                                                [
                                                                  [
                                                                    [
                                                                      [
                                                                        {
                                                                          [
                                                                            {
                                                                              Extended_match
                                                                              (con integer)
                                                                            }
                                                                            ww
                                                                          ]
                                                                          (fun Unit Bool)
                                                                        }
                                                                        (lam
                                                                          ipv
                                                                          (con integer)
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
                                                                                          ipv
                                                                                        ]
                                                                                        ipv
                                                                                      ]
                                                                                    ]
                                                                                    (fun Unit Bool)
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
                                                                                              ww
                                                                                            ]
                                                                                            (fun Unit Bool)
                                                                                          }
                                                                                          (lam
                                                                                            thunk
                                                                                            Unit
                                                                                            ww
                                                                                          )
                                                                                        ]
                                                                                        (lam
                                                                                          thunk
                                                                                          Unit
                                                                                          True
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
                                                                                    [
                                                                                      lessThanEqInteger
                                                                                      ipv
                                                                                    ]
                                                                                    ipv
                                                                                  ]
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
                                                                          (abs
                                                                            e
                                                                            (type)
                                                                            (error
                                                                              e
                                                                            )
                                                                          )
                                                                          Bool
                                                                        }
                                                                      )
                                                                    ]
                                                                    (lam
                                                                      thunk
                                                                      Unit
                                                                      True
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
                                                              (abs
                                                                e
                                                                (type)
                                                                (error e)
                                                              )
                                                              Bool
                                                            }
                                                          )
                                                        ]
                                                        (lam
                                                          thunk
                                                          Unit
                                                          [
                                                            [
                                                              [
                                                                [
                                                                  {
                                                                    [
                                                                      {
                                                                        Extended_match
                                                                        (con integer)
                                                                      }
                                                                      ww
                                                                    ]
                                                                    (fun Unit Bool)
                                                                  }
                                                                  (lam
                                                                    ipv
                                                                    (con integer)
                                                                    (lam
                                                                      thunk
                                                                      Unit
                                                                      False
                                                                    )
                                                                  )
                                                                ]
                                                                (lam
                                                                  thunk
                                                                  Unit
                                                                  {
                                                                    (abs
                                                                      e
                                                                      (type)
                                                                      (error e)
                                                                    )
                                                                    Bool
                                                                  }
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
                                                                          ww
                                                                        ]
                                                                        (fun Unit Bool)
                                                                      }
                                                                      (lam
                                                                        thunk
                                                                        Unit
                                                                        ww
                                                                      )
                                                                    ]
                                                                    (lam
                                                                      thunk
                                                                      Unit
                                                                      True
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
                                                      Unit
                                                    ]
                                                  )
                                                )
                                              ]
                                              (lam thunk Unit False)
                                            ]
                                            (lam
                                              thunk
                                              Unit
                                              [
                                                [
                                                  [
                                                    [
                                                      {
                                                        [
                                                          {
                                                            Extended_match
                                                            (con integer)
                                                          }
                                                          ww
                                                        ]
                                                        (fun Unit Bool)
                                                      }
                                                      (lam
                                                        ipv
                                                        (con integer)
                                                        (lam
                                                          thunk
                                                          Unit
                                                          [
                                                            [
                                                              [
                                                                [
                                                                  {
                                                                    [
                                                                      {
                                                                        Extended_match
                                                                        (con integer)
                                                                      }
                                                                      ww
                                                                    ]
                                                                    (fun Unit Bool)
                                                                  }
                                                                  (lam
                                                                    ipv
                                                                    (con integer)
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
                                                                                    ipv
                                                                                  ]
                                                                                  ipv
                                                                                ]
                                                                              ]
                                                                              (fun Unit Bool)
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
                                                                                        ww
                                                                                      ]
                                                                                      (fun Unit Bool)
                                                                                    }
                                                                                    (lam
                                                                                      thunk
                                                                                      Unit
                                                                                      ww
                                                                                    )
                                                                                  ]
                                                                                  (lam
                                                                                    thunk
                                                                                    Unit
                                                                                    True
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
                                                                              [
                                                                                lessThanEqInteger
                                                                                ipv
                                                                              ]
                                                                              ipv
                                                                            ]
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
                                                                    (abs
                                                                      e
                                                                      (type)
                                                                      (error e)
                                                                    )
                                                                    Bool
                                                                  }
                                                                )
                                                              ]
                                                              (lam
                                                                thunk Unit True
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
                                                        (abs e (type) (error e))
                                                        Bool
                                                      }
                                                    )
                                                  ]
                                                  (lam
                                                    thunk
                                                    Unit
                                                    [
                                                      [
                                                        [
                                                          [
                                                            {
                                                              [
                                                                {
                                                                  Extended_match
                                                                  (con integer)
                                                                }
                                                                ww
                                                              ]
                                                              (fun Unit Bool)
                                                            }
                                                            (lam
                                                              ipv
                                                              (con integer)
                                                              (lam
                                                                thunk Unit False
                                                              )
                                                            )
                                                          ]
                                                          (lam
                                                            thunk
                                                            Unit
                                                            {
                                                              (abs
                                                                e
                                                                (type)
                                                                (error e)
                                                              )
                                                              Bool
                                                            }
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
                                                                    ww
                                                                  ]
                                                                  (fun Unit Bool)
                                                                }
                                                                (lam
                                                                  thunk Unit ww
                                                                )
                                                              ]
                                                              (lam
                                                                thunk Unit True
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
                                                Unit
                                              ]
                                            )
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
                            sfOrdUpperBound0_c
                            (fun [UpperBound (con integer)] (fun [UpperBound (con integer)] Bool))
                          )
                          (lam
                            w
                            [UpperBound (con integer)]
                            (lam
                              w
                              [UpperBound (con integer)]
                              [
                                {
                                  [ { UpperBound_match (con integer) } w ] Bool
                                }
                                (lam
                                  ww
                                  [Extended (con integer)]
                                  (lam
                                    ww
                                    Bool
                                    [
                                      {
                                        [ { UpperBound_match (con integer) } w ]
                                        Bool
                                      }
                                      (lam
                                        ww
                                        [Extended (con integer)]
                                        (lam
                                          ww
                                          Bool
                                          [
                                            [
                                              [ [ wsfOrdUpperBound0_c ww ] ww ]
                                              ww
                                            ]
                                            ww
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
                        (termbind
                          (strict)
                          (vardecl
                            wscontains
                            (fun [Extended (con integer)] (fun Bool (fun [UpperBound (con integer)] (fun [Extended (con integer)] (fun Bool (fun [UpperBound (con integer)] Bool))))))
                          )
                          (lam
                            ww
                            [Extended (con integer)]
                            (lam
                              ww
                              Bool
                              (lam
                                ww
                                [UpperBound (con integer)]
                                (lam
                                  ww
                                  [Extended (con integer)]
                                  (lam
                                    ww
                                    Bool
                                    (lam
                                      ww
                                      [UpperBound (con integer)]
                                      (let
                                        (nonrec)
                                        (termbind
                                          (nonstrict)
                                          (vardecl j Bool)
                                          [
                                            [
                                              [
                                                {
                                                  [ Bool_match ww ]
                                                  (fun Unit Bool)
                                                }
                                                (lam
                                                  thunk
                                                  Unit
                                                  [
                                                    [
                                                      [
                                                        {
                                                          [ Bool_match ww ]
                                                          (fun Unit Bool)
                                                        }
                                                        (lam
                                                          thunk
                                                          Unit
                                                          [
                                                            [
                                                              sfOrdUpperBound0_c
                                                              ww
                                                            ]
                                                            ww
                                                          ]
                                                        )
                                                      ]
                                                      (lam thunk Unit False)
                                                    ]
                                                    Unit
                                                  ]
                                                )
                                              ]
                                              (lam
                                                thunk
                                                Unit
                                                [ [ sfOrdUpperBound0_c ww ] ww ]
                                              )
                                            ]
                                            Unit
                                          ]
                                        )
                                        [
                                          [
                                            [
                                              [
                                                {
                                                  [
                                                    {
                                                      Extended_match
                                                      (con integer)
                                                    }
                                                    ww
                                                  ]
                                                  (fun Unit Bool)
                                                }
                                                (lam
                                                  default_arg0
                                                  (con integer)
                                                  (lam
                                                    thunk
                                                    Unit
                                                    [
                                                      [
                                                        [
                                                          [
                                                            {
                                                              [
                                                                {
                                                                  Extended_match
                                                                  (con integer)
                                                                }
                                                                ww
                                                              ]
                                                              (fun Unit Bool)
                                                            }
                                                            (lam
                                                              default_arg0
                                                              (con integer)
                                                              (lam
                                                                thunk
                                                                Unit
                                                                [
                                                                  [
                                                                    [
                                                                      [
                                                                        {
                                                                          [
                                                                            {
                                                                              Extended_match
                                                                              (con integer)
                                                                            }
                                                                            ww
                                                                          ]
                                                                          (fun Unit Bool)
                                                                        }
                                                                        (lam
                                                                          ipv
                                                                          (con integer)
                                                                          (lam
                                                                            thunk
                                                                            Unit
                                                                            [
                                                                              [
                                                                                [
                                                                                  [
                                                                                    {
                                                                                      [
                                                                                        {
                                                                                          Extended_match
                                                                                          (con integer)
                                                                                        }
                                                                                        ww
                                                                                      ]
                                                                                      (fun Unit Bool)
                                                                                    }
                                                                                    (lam
                                                                                      ipv
                                                                                      (con integer)
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
                                                                                                      ipv
                                                                                                    ]
                                                                                                    ipv
                                                                                                  ]
                                                                                                ]
                                                                                                (fun Unit Bool)
                                                                                              }
                                                                                              (lam
                                                                                                thunk
                                                                                                Unit
                                                                                                j
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
                                                                                                            lessThanEqInteger
                                                                                                            ipv
                                                                                                          ]
                                                                                                          ipv
                                                                                                        ]
                                                                                                      ]
                                                                                                      (fun Unit Bool)
                                                                                                    }
                                                                                                    (lam
                                                                                                      thunk
                                                                                                      Unit
                                                                                                      [
                                                                                                        [
                                                                                                          sfOrdUpperBound0_c
                                                                                                          ww
                                                                                                        ]
                                                                                                        ww
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
                                                                                          Unit
                                                                                        ]
                                                                                      )
                                                                                    )
                                                                                  ]
                                                                                  (lam
                                                                                    thunk
                                                                                    Unit
                                                                                    {
                                                                                      (abs
                                                                                        e
                                                                                        (type)
                                                                                        (error
                                                                                          e
                                                                                        )
                                                                                      )
                                                                                      Bool
                                                                                    }
                                                                                  )
                                                                                ]
                                                                                (lam
                                                                                  thunk
                                                                                  Unit
                                                                                  [
                                                                                    [
                                                                                      sfOrdUpperBound0_c
                                                                                      ww
                                                                                    ]
                                                                                    ww
                                                                                  ]
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
                                                                          (abs
                                                                            e
                                                                            (type)
                                                                            (error
                                                                              e
                                                                            )
                                                                          )
                                                                          Bool
                                                                        }
                                                                      )
                                                                    ]
                                                                    (lam
                                                                      thunk
                                                                      Unit
                                                                      [
                                                                        [
                                                                          [
                                                                            [
                                                                              {
                                                                                [
                                                                                  {
                                                                                    Extended_match
                                                                                    (con integer)
                                                                                  }
                                                                                  ww
                                                                                ]
                                                                                (fun Unit Bool)
                                                                              }
                                                                              (lam
                                                                                ipv
                                                                                (con integer)
                                                                                (lam
                                                                                  thunk
                                                                                  Unit
                                                                                  False
                                                                                )
                                                                              )
                                                                            ]
                                                                            (lam
                                                                              thunk
                                                                              Unit
                                                                              {
                                                                                (abs
                                                                                  e
                                                                                  (type)
                                                                                  (error
                                                                                    e
                                                                                  )
                                                                                )
                                                                                Bool
                                                                              }
                                                                            )
                                                                          ]
                                                                          (lam
                                                                            thunk
                                                                            Unit
                                                                            j
                                                                          )
                                                                        ]
                                                                        Unit
                                                                      ]
                                                                    )
                                                                  ]
                                                                  Unit
                                                                ]
                                                              )
                                                            )
                                                          ]
                                                          (lam thunk Unit False)
                                                        ]
                                                        (lam
                                                          thunk
                                                          Unit
                                                          [
                                                            [
                                                              [
                                                                [
                                                                  {
                                                                    [
                                                                      {
                                                                        Extended_match
                                                                        (con integer)
                                                                      }
                                                                      ww
                                                                    ]
                                                                    (fun Unit Bool)
                                                                  }
                                                                  (lam
                                                                    ipv
                                                                    (con integer)
                                                                    (lam
                                                                      thunk
                                                                      Unit
                                                                      [
                                                                        [
                                                                          [
                                                                            [
                                                                              {
                                                                                [
                                                                                  {
                                                                                    Extended_match
                                                                                    (con integer)
                                                                                  }
                                                                                  ww
                                                                                ]
                                                                                (fun Unit Bool)
                                                                              }
                                                                              (lam
                                                                                ipv
                                                                                (con integer)
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
                                                                                                ipv
                                                                                              ]
                                                                                              ipv
                                                                                            ]
                                                                                          ]
                                                                                          (fun Unit Bool)
                                                                                        }
                                                                                        (lam
                                                                                          thunk
                                                                                          Unit
                                                                                          j
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
                                                                                                      lessThanEqInteger
                                                                                                      ipv
                                                                                                    ]
                                                                                                    ipv
                                                                                                  ]
                                                                                                ]
                                                                                                (fun Unit Bool)
                                                                                              }
                                                                                              (lam
                                                                                                thunk
                                                                                                Unit
                                                                                                [
                                                                                                  [
                                                                                                    sfOrdUpperBound0_c
                                                                                                    ww
                                                                                                  ]
                                                                                                  ww
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
                                                                                    Unit
                                                                                  ]
                                                                                )
                                                                              )
                                                                            ]
                                                                            (lam
                                                                              thunk
                                                                              Unit
                                                                              {
                                                                                (abs
                                                                                  e
                                                                                  (type)
                                                                                  (error
                                                                                    e
                                                                                  )
                                                                                )
                                                                                Bool
                                                                              }
                                                                            )
                                                                          ]
                                                                          (lam
                                                                            thunk
                                                                            Unit
                                                                            [
                                                                              [
                                                                                sfOrdUpperBound0_c
                                                                                ww
                                                                              ]
                                                                              ww
                                                                            ]
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
                                                                    (abs
                                                                      e
                                                                      (type)
                                                                      (error e)
                                                                    )
                                                                    Bool
                                                                  }
                                                                )
                                                              ]
                                                              (lam
                                                                thunk
                                                                Unit
                                                                [
                                                                  [
                                                                    [
                                                                      [
                                                                        {
                                                                          [
                                                                            {
                                                                              Extended_match
                                                                              (con integer)
                                                                            }
                                                                            ww
                                                                          ]
                                                                          (fun Unit Bool)
                                                                        }
                                                                        (lam
                                                                          ipv
                                                                          (con integer)
                                                                          (lam
                                                                            thunk
                                                                            Unit
                                                                            False
                                                                          )
                                                                        )
                                                                      ]
                                                                      (lam
                                                                        thunk
                                                                        Unit
                                                                        {
                                                                          (abs
                                                                            e
                                                                            (type)
                                                                            (error
                                                                              e
                                                                            )
                                                                          )
                                                                          Bool
                                                                        }
                                                                      )
                                                                    ]
                                                                    (lam
                                                                      thunk
                                                                      Unit
                                                                      j
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
                                                      Unit
                                                    ]
                                                  )
                                                )
                                              ]
                                              (lam
                                                thunk
                                                Unit
                                                [
                                                  [
                                                    [
                                                      [
                                                        {
                                                          [
                                                            {
                                                              Extended_match
                                                              (con integer)
                                                            }
                                                            ww
                                                          ]
                                                          (fun Unit Bool)
                                                        }
                                                        (lam
                                                          default_arg0
                                                          (con integer)
                                                          (lam
                                                            thunk
                                                            Unit
                                                            [
                                                              [
                                                                sfOrdUpperBound0_c
                                                                ww
                                                              ]
                                                              ww
                                                            ]
                                                          )
                                                        )
                                                      ]
                                                      (lam thunk Unit j)
                                                    ]
                                                    (lam
                                                      thunk
                                                      Unit
                                                      [
                                                        [
                                                          sfOrdUpperBound0_c ww
                                                        ]
                                                        ww
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
                                                [
                                                  [
                                                    [
                                                      {
                                                        [
                                                          {
                                                            Extended_match
                                                            (con integer)
                                                          }
                                                          ww
                                                        ]
                                                        (fun Unit Bool)
                                                      }
                                                      (lam
                                                        default_arg0
                                                        (con integer)
                                                        (lam
                                                          thunk
                                                          Unit
                                                          [
                                                            [
                                                              [
                                                                [
                                                                  {
                                                                    [
                                                                      {
                                                                        Extended_match
                                                                        (con integer)
                                                                      }
                                                                      ww
                                                                    ]
                                                                    (fun Unit Bool)
                                                                  }
                                                                  (lam
                                                                    ipv
                                                                    (con integer)
                                                                    (lam
                                                                      thunk
                                                                      Unit
                                                                      [
                                                                        [
                                                                          [
                                                                            [
                                                                              {
                                                                                [
                                                                                  {
                                                                                    Extended_match
                                                                                    (con integer)
                                                                                  }
                                                                                  ww
                                                                                ]
                                                                                (fun Unit Bool)
                                                                              }
                                                                              (lam
                                                                                ipv
                                                                                (con integer)
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
                                                                                                ipv
                                                                                              ]
                                                                                              ipv
                                                                                            ]
                                                                                          ]
                                                                                          (fun Unit Bool)
                                                                                        }
                                                                                        (lam
                                                                                          thunk
                                                                                          Unit
                                                                                          j
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
                                                                                                      lessThanEqInteger
                                                                                                      ipv
                                                                                                    ]
                                                                                                    ipv
                                                                                                  ]
                                                                                                ]
                                                                                                (fun Unit Bool)
                                                                                              }
                                                                                              (lam
                                                                                                thunk
                                                                                                Unit
                                                                                                [
                                                                                                  [
                                                                                                    sfOrdUpperBound0_c
                                                                                                    ww
                                                                                                  ]
                                                                                                  ww
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
                                                                                    Unit
                                                                                  ]
                                                                                )
                                                                              )
                                                                            ]
                                                                            (lam
                                                                              thunk
                                                                              Unit
                                                                              {
                                                                                (abs
                                                                                  e
                                                                                  (type)
                                                                                  (error
                                                                                    e
                                                                                  )
                                                                                )
                                                                                Bool
                                                                              }
                                                                            )
                                                                          ]
                                                                          (lam
                                                                            thunk
                                                                            Unit
                                                                            [
                                                                              [
                                                                                sfOrdUpperBound0_c
                                                                                ww
                                                                              ]
                                                                              ww
                                                                            ]
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
                                                                    (abs
                                                                      e
                                                                      (type)
                                                                      (error e)
                                                                    )
                                                                    Bool
                                                                  }
                                                                )
                                                              ]
                                                              (lam
                                                                thunk
                                                                Unit
                                                                [
                                                                  [
                                                                    [
                                                                      [
                                                                        {
                                                                          [
                                                                            {
                                                                              Extended_match
                                                                              (con integer)
                                                                            }
                                                                            ww
                                                                          ]
                                                                          (fun Unit Bool)
                                                                        }
                                                                        (lam
                                                                          ipv
                                                                          (con integer)
                                                                          (lam
                                                                            thunk
                                                                            Unit
                                                                            False
                                                                          )
                                                                        )
                                                                      ]
                                                                      (lam
                                                                        thunk
                                                                        Unit
                                                                        {
                                                                          (abs
                                                                            e
                                                                            (type)
                                                                            (error
                                                                              e
                                                                            )
                                                                          )
                                                                          Bool
                                                                        }
                                                                      )
                                                                    ]
                                                                    (lam
                                                                      thunk
                                                                      Unit
                                                                      j
                                                                    )
                                                                  ]
                                                                  Unit
                                                                ]
                                                              )
                                                            ]
                                                            Unit
                                                          ]
                                                        )
                                                      )
                                                    ]
                                                    (lam thunk Unit False)
                                                  ]
                                                  (lam
                                                    thunk
                                                    Unit
                                                    [
                                                      [
                                                        [
                                                          [
                                                            {
                                                              [
                                                                {
                                                                  Extended_match
                                                                  (con integer)
                                                                }
                                                                ww
                                                              ]
                                                              (fun Unit Bool)
                                                            }
                                                            (lam
                                                              ipv
                                                              (con integer)
                                                              (lam
                                                                thunk
                                                                Unit
                                                                [
                                                                  [
                                                                    [
                                                                      [
                                                                        {
                                                                          [
                                                                            {
                                                                              Extended_match
                                                                              (con integer)
                                                                            }
                                                                            ww
                                                                          ]
                                                                          (fun Unit Bool)
                                                                        }
                                                                        (lam
                                                                          ipv
                                                                          (con integer)
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
                                                                                          ipv
                                                                                        ]
                                                                                        ipv
                                                                                      ]
                                                                                    ]
                                                                                    (fun Unit Bool)
                                                                                  }
                                                                                  (lam
                                                                                    thunk
                                                                                    Unit
                                                                                    j
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
                                                                                                lessThanEqInteger
                                                                                                ipv
                                                                                              ]
                                                                                              ipv
                                                                                            ]
                                                                                          ]
                                                                                          (fun Unit Bool)
                                                                                        }
                                                                                        (lam
                                                                                          thunk
                                                                                          Unit
                                                                                          [
                                                                                            [
                                                                                              sfOrdUpperBound0_c
                                                                                              ww
                                                                                            ]
                                                                                            ww
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
                                                                              Unit
                                                                            ]
                                                                          )
                                                                        )
                                                                      ]
                                                                      (lam
                                                                        thunk
                                                                        Unit
                                                                        {
                                                                          (abs
                                                                            e
                                                                            (type)
                                                                            (error
                                                                              e
                                                                            )
                                                                          )
                                                                          Bool
                                                                        }
                                                                      )
                                                                    ]
                                                                    (lam
                                                                      thunk
                                                                      Unit
                                                                      [
                                                                        [
                                                                          sfOrdUpperBound0_c
                                                                          ww
                                                                        ]
                                                                        ww
                                                                      ]
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
                                                              (abs
                                                                e
                                                                (type)
                                                                (error e)
                                                              )
                                                              Bool
                                                            }
                                                          )
                                                        ]
                                                        (lam
                                                          thunk
                                                          Unit
                                                          [
                                                            [
                                                              [
                                                                [
                                                                  {
                                                                    [
                                                                      {
                                                                        Extended_match
                                                                        (con integer)
                                                                      }
                                                                      ww
                                                                    ]
                                                                    (fun Unit Bool)
                                                                  }
                                                                  (lam
                                                                    ipv
                                                                    (con integer)
                                                                    (lam
                                                                      thunk
                                                                      Unit
                                                                      False
                                                                    )
                                                                  )
                                                                ]
                                                                (lam
                                                                  thunk
                                                                  Unit
                                                                  {
                                                                    (abs
                                                                      e
                                                                      (type)
                                                                      (error e)
                                                                    )
                                                                    Bool
                                                                  }
                                                                )
                                                              ]
                                                              (lam thunk Unit j)
                                                            ]
                                                            Unit
                                                          ]
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
                          (strict)
                          (vardecl
                            scontains
                            (fun [Interval (con integer)] (fun [Interval (con integer)] Bool))
                          )
                          (lam
                            w
                            [Interval (con integer)]
                            (lam
                              w
                              [Interval (con integer)]
                              [
                                { [ { Interval_match (con integer) } w ] Bool }
                                (lam
                                  ww
                                  [LowerBound (con integer)]
                                  (lam
                                    ww
                                    [UpperBound (con integer)]
                                    [
                                      {
                                        [
                                          { LowerBound_match (con integer) } ww
                                        ]
                                        Bool
                                      }
                                      (lam
                                        ww
                                        [Extended (con integer)]
                                        (lam
                                          ww
                                          Bool
                                          [
                                            {
                                              [
                                                { Interval_match (con integer) }
                                                w
                                              ]
                                              Bool
                                            }
                                            (lam
                                              ww
                                              [LowerBound (con integer)]
                                              (lam
                                                ww
                                                [UpperBound (con integer)]
                                                [
                                                  {
                                                    [
                                                      {
                                                        LowerBound_match
                                                        (con integer)
                                                      }
                                                      ww
                                                    ]
                                                    Bool
                                                  }
                                                  (lam
                                                    ww
                                                    [Extended (con integer)]
                                                    (lam
                                                      ww
                                                      Bool
                                                      [
                                                        [
                                                          [
                                                            [
                                                              [
                                                                [
                                                                  wscontains ww
                                                                ]
                                                                ww
                                                              ]
                                                              ww
                                                            ]
                                                            ww
                                                          ]
                                                          ww
                                                        ]
                                                        ww
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
                              ]
                            )
                          )
                        )
                        (datatypebind
                          (datatype
                            (tyvardecl Campaign (type))

                            Campaign_match
                            (vardecl
                              Campaign
                              (fun (con integer) (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun (con integer) (fun (con bytestring) Campaign))))
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
                                [
                                  [
                                    [
                                      {
                                        [ { Maybe_match a } ds ]
                                        (fun Unit [(lam a (type) [Maybe a]) a])
                                      }
                                      (lam ipv a (lam thunk Unit ds))
                                    ]
                                    (lam thunk Unit b)
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
                                          [Interval (con integer)]
                                          (lam
                                            ds
                                            [List (con bytestring)]
                                            (lam
                                              ds
                                              [List (con bytestring)]
                                              (lam
                                                ds
                                                [List [[Tuple2 (con bytestring)] Data]]
                                                (lam
                                                  ds
                                                  (con bytestring)
                                                  (let
                                                    (nonrec)
                                                    (termbind
                                                      (nonstrict)
                                                      (vardecl
                                                        p
                                                        (fun (con bytestring) Bool)
                                                      )
                                                      [ equalsByteString k ]
                                                    )
                                                    [
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
                                                                    [
                                                                      [
                                                                        [
                                                                          {
                                                                            [
                                                                              Bool_match
                                                                              [
                                                                                p
                                                                                x
                                                                              ]
                                                                            ]
                                                                            (fun Unit [Maybe (con bytestring)])
                                                                          }
                                                                          (lam
                                                                            thunk
                                                                            Unit
                                                                            [
                                                                              {
                                                                                Just
                                                                                (con bytestring)
                                                                              }
                                                                              x
                                                                            ]
                                                                          )
                                                                        ]
                                                                        (lam
                                                                          thunk
                                                                          Unit
                                                                          {
                                                                            Nothing
                                                                            (con bytestring)
                                                                          }
                                                                        )
                                                                      ]
                                                                      Unit
                                                                    ]
                                                                  )
                                                                ]
                                                                ds
                                                              ]
                                                            ]
                                                            (fun Unit Bool)
                                                          }
                                                          (lam
                                                            ds
                                                            (con bytestring)
                                                            (lam thunk Unit True
                                                            )
                                                          )
                                                        ]
                                                        (lam thunk Unit False)
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
                                  )
                                )
                              ]
                            )
                          )
                        )
                        (termbind
                          (strict)
                          (vardecl
                            validCollection (fun Campaign (fun TxInfo Bool))
                          )
                          (lam
                            campaign
                            Campaign
                            (lam
                              txinfo
                              TxInfo
                              [
                                { [ TxInfo_match txinfo ] Bool }
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
                                          [Interval (con integer)]
                                          (lam
                                            ds
                                            [List (con bytestring)]
                                            (lam
                                              ds
                                              [List (con bytestring)]
                                              (lam
                                                ds
                                                [List [[Tuple2 (con bytestring)] Data]]
                                                (lam
                                                  ds
                                                  (con bytestring)
                                                  [
                                                    [
                                                      [
                                                        {
                                                          [
                                                            Bool_match
                                                            [
                                                              [
                                                                scontains
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
                                                                                Campaign_match
                                                                                campaign
                                                                              ]
                                                                              (con integer)
                                                                            }
                                                                            (lam
                                                                              ds
                                                                              (con integer)
                                                                              (lam
                                                                                ds
                                                                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                (lam
                                                                                  ds
                                                                                  (con integer)
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
                                                                          {
                                                                            [
                                                                              Campaign_match
                                                                              campaign
                                                                            ]
                                                                            (con integer)
                                                                          }
                                                                          (lam
                                                                            ds
                                                                            (con integer)
                                                                            (lam
                                                                              ds
                                                                              [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                              (lam
                                                                                ds
                                                                                (con integer)
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
                                                                    ]
                                                                    True
                                                                  ]
                                                                ]
                                                              ]
                                                              ds
                                                            ]
                                                          ]
                                                          (fun Unit Bool)
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
                                                                        [
                                                                          checkBinRel
                                                                          greaterThanEqInteger
                                                                        ]
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
                                                                            txInInfoValue
                                                                          ]
                                                                          ds
                                                                        ]
                                                                      ]
                                                                      [
                                                                        {
                                                                          [
                                                                            Campaign_match
                                                                            campaign
                                                                          ]
                                                                          [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                        }
                                                                        (lam
                                                                          ds
                                                                          (con integer)
                                                                          (lam
                                                                            ds
                                                                            [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                            (lam
                                                                              ds
                                                                              (con integer)
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
                                                                  ]
                                                                  (fun Unit Bool)
                                                                }
                                                                (lam
                                                                  thunk
                                                                  Unit
                                                                  [
                                                                    [
                                                                      txSignedBy
                                                                      txinfo
                                                                    ]
                                                                    [
                                                                      {
                                                                        [
                                                                          Campaign_match
                                                                          campaign
                                                                        ]
                                                                        (con bytestring)
                                                                      }
                                                                      (lam
                                                                        ds
                                                                        (con integer)
                                                                        (lam
                                                                          ds
                                                                          [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                          (lam
                                                                            ds
                                                                            (con integer)
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
                                                                )
                                                              ]
                                                              (lam
                                                                thunk Unit False
                                                              )
                                                            ]
                                                            Unit
                                                          ]
                                                        )
                                                      ]
                                                      (lam thunk Unit False)
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
                                )
                              ]
                            )
                          )
                        )
                        (termbind
                          (strict)
                          (vardecl
                            validRefund
                            (fun Campaign (fun (con bytestring) (fun TxInfo Bool)))
                          )
                          (lam
                            campaign
                            Campaign
                            (lam
                              contributor
                              (con bytestring)
                              (lam
                                txinfo
                                TxInfo
                                [
                                  { [ TxInfo_match txinfo ] Bool }
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
                                            [Interval (con integer)]
                                            (lam
                                              ds
                                              [List (con bytestring)]
                                              (lam
                                                ds
                                                [List (con bytestring)]
                                                (lam
                                                  ds
                                                  [List [[Tuple2 (con bytestring)] Data]]
                                                  (lam
                                                    ds
                                                    (con bytestring)
                                                    [
                                                      [
                                                        [
                                                          {
                                                            [
                                                              Bool_match
                                                              [
                                                                [
                                                                  scontains
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
                                                                                  Campaign_match
                                                                                  campaign
                                                                                ]
                                                                                (con integer)
                                                                              }
                                                                              (lam
                                                                                ds
                                                                                (con integer)
                                                                                (lam
                                                                                  ds
                                                                                  [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                  (lam
                                                                                    ds
                                                                                    (con integer)
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
                                                                ds
                                                              ]
                                                            ]
                                                            (fun Unit Bool)
                                                          }
                                                          (lam
                                                            thunk
                                                            Unit
                                                            [
                                                              [
                                                                txSignedBy
                                                                txinfo
                                                              ]
                                                              contributor
                                                            ]
                                                          )
                                                        ]
                                                        (lam thunk Unit False)
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
                                  )
                                ]
                              )
                            )
                          )
                        )
                        (termbind
                          (strict)
                          (vardecl
                            mkValidator
                            (fun Campaign (fun (con bytestring) (fun CampaignAction (fun ValidatorCtx Bool))))
                          )
                          (lam
                            c
                            Campaign
                            (lam
                              con
                              (con bytestring)
                              (lam
                                act
                                CampaignAction
                                (lam
                                  p
                                  ValidatorCtx
                                  [
                                    [
                                      [
                                        {
                                          [ CampaignAction_match act ]
                                          (fun Unit Bool)
                                        }
                                        (lam
                                          thunk
                                          Unit
                                          [
                                            { [ ValidatorCtx_match p ] Bool }
                                            (lam
                                              ds
                                              TxInfo
                                              (lam
                                                ds
                                                (con integer)
                                                [ [ validCollection c ] ds ]
                                              )
                                            )
                                          ]
                                        )
                                      ]
                                      (lam
                                        thunk
                                        Unit
                                        [
                                          { [ ValidatorCtx_match p ] Bool }
                                          (lam
                                            ds
                                            TxInfo
                                            (lam
                                              ds
                                              (con integer)
                                              [ [ [ validRefund c ] con ] ds ]
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