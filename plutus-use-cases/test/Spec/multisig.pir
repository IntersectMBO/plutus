(program
  (let
    (nonrec)
    (datatypebind
      (datatype
        (tyvardecl Bool (type))

        Bool_match
        (vardecl True Bool) (vardecl False Bool)
      )
    )
    (termbind
      (strict)
      (vardecl
        equalsByteString (fun (con bytestring) (fun (con bytestring) Bool))
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
      (datatype (tyvardecl Unit (type))  Unit_match (vardecl Unit Unit))
    )
    (datatypebind
      (datatype
        (tyvardecl Maybe (fun (type) (type)))
        (tyvardecl a (type))
        Maybe_match
        (vardecl Just (fun a [Maybe a])) (vardecl Nothing [Maybe a])
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
            find (all a (type) (fun (fun a Bool) (fun [List a] [Maybe a])))
          )
          (abs
            a
            (type)
            (lam
              p
              (fun a Bool)
              (let
                (rec)
                (termbind
                  (strict)
                  (vardecl go (fun [List a] [Maybe a]))
                  (lam
                    l
                    [List a]
                    [
                      [
                        [
                          { [ { Nil_match a } l ] (fun Unit [Maybe a]) }
                          (lam thunk Unit { Nothing a })
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
                                  [
                                    {
                                      [ Bool_match [ p x ] ]
                                      (fun Unit [Maybe a])
                                    }
                                    (lam thunk Unit [ { Just a } x ])
                                  ]
                                  (lam thunk Unit [ go xs ])
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
                go
              )
            )
          )
        )
        (termbind
          (strict)
          (vardecl
            greaterThanEqInteger (fun (con integer) (fun (con integer) Bool))
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
                  [ [ [ { (builtin ifThenElse) Bool } b ] True ] False ]
                )
                [ [ (builtin greaterThanEqualsInteger) arg ] arg ]
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
                                  [ f x ] [ [ [ { { foldr a } b } f ] acc ] xs ]
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
              (vardecl length (all a (type) (fun [List a] (con integer))))
              (abs
                a
                (type)
                [
                  [
                    { { foldr a } (con integer) }
                    (lam
                      ds
                      a
                      (lam
                        acc
                        (con integer)
                        [ [ (builtin addInteger) acc ] (con integer 1) ]
                      )
                    )
                  ]
                  (con integer 0)
                ]
              )
            )
            (termbind
              (strict)
              (vardecl trace (fun (con string) Unit))
              (lam
                arg
                (con string)
                [ (lam b (con unit) Unit) [ (builtin trace) arg ] ]
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
                    (vardecl
                      LowerBound (fun [Extended a] (fun Bool [LowerBound a]))
                    )
                  )
                )
                (datatypebind
                  (datatype
                    (tyvardecl UpperBound (fun (type) (type)))
                    (tyvardecl a (type))
                    UpperBound_match
                    (vardecl
                      UpperBound (fun [Extended a] (fun Bool [UpperBound a]))
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
                    (tyvardecl
                      Tuple3 (fun (type) (fun (type) (fun (type) (type))))
                    )
                    (tyvardecl a (type))
                    (tyvardecl b (type))
                    (tyvardecl c (type))
                    Tuple3_match
                    (vardecl Tuple3 (fun a (fun b (fun c [[[Tuple3 a] b] c]))))
                  )
                )
                (datatypebind
                  (datatype
                    (tyvardecl TxOutRef (type))

                    TxOutRef_match
                    (vardecl
                      TxOutRef
                      (fun (con bytestring) (fun (con integer) TxOutRef))
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
                (termbind
                  (strict)
                  (vardecl
                    wvalidate
                    (fun [List (con bytestring)] (fun (con integer) (fun ValidatorCtx Bool)))
                  )
                  (lam
                    ww
                    [List (con bytestring)]
                    (lam
                      ww
                      (con integer)
                      (lam
                        w
                        ValidatorCtx
                        [
                          [
                            [
                              {
                                [
                                  Bool_match
                                  [
                                    [
                                      greaterThanEqInteger
                                      [
                                        { length (con bytestring) }
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
                                                  [
                                                    {
                                                      [ ValidatorCtx_match w ]
                                                      [List (con bytestring)]
                                                    }
                                                    (lam
                                                      ds
                                                      TxInfo
                                                      (lam
                                                        ds
                                                        (con integer)
                                                        [
                                                          {
                                                            [ TxInfo_match ds ]
                                                            [List (con bytestring)]
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
                                                                                      {
                                                                                        Maybe_match
                                                                                        (con bytestring)
                                                                                      }
                                                                                      [
                                                                                        [
                                                                                          {
                                                                                            find
                                                                                            (con bytestring)
                                                                                          }
                                                                                          [
                                                                                            equalsByteString
                                                                                            e
                                                                                          ]
                                                                                        ]
                                                                                        ds
                                                                                      ]
                                                                                    ]
                                                                                    (fun Unit [List (con bytestring)])
                                                                                  }
                                                                                  (lam
                                                                                    ds
                                                                                    (con bytestring)
                                                                                    (lam
                                                                                      thunk
                                                                                      Unit
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
                                                                                  )
                                                                                ]
                                                                                (lam
                                                                                  thunk
                                                                                  Unit
                                                                                  xs
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
                                                          )
                                                        ]
                                                      )
                                                    )
                                                  ]
                                                )
                                              )
                                            ]
                                            { Nil (con bytestring) }
                                          ]
                                          ww
                                        ]
                                      ]
                                    ]
                                    ww
                                  ]
                                ]
                                (fun Unit Bool)
                              }
                              (lam thunk Unit True)
                            ]
                            (lam
                              thunk
                              Unit
                              [
                                [
                                  {
                                    [
                                      Unit_match
                                      [
                                        trace
                                        (con string "not enough signatures")
                                      ]
                                    ]
                                    (fun Unit Bool)
                                  }
                                  (lam thunk Unit False)
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
                (datatypebind
                  (datatype
                    (tyvardecl MultiSig (type))

                    MultiSig_match
                    (vardecl
                      MultiSig
                      (fun [List (con bytestring)] (fun (con integer) MultiSig))
                    )
                  )
                )
                (termbind
                  (strict)
                  (vardecl
                    validate
                    (fun MultiSig (fun Unit (fun Unit (fun ValidatorCtx Bool))))
                  )
                  (lam
                    w
                    MultiSig
                    (lam
                      w
                      Unit
                      (lam
                        w
                        Unit
                        (lam
                          w
                          ValidatorCtx
                          [
                            { [ MultiSig_match w ] Bool }
                            (lam
                              ww
                              [List (con bytestring)]
                              (lam
                                ww (con integer) [ [ [ wvalidate ww ] ww ] w ]
                              )
                            )
                          ]
                        )
                      )
                    )
                  )
                )
                validate
              )
            )
          )
        )
      )
    )
  )
)