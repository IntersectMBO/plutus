(program
  (let
    (nonrec)
    (datatypebind
      (datatype (tyvardecl Unit (type))  Unit_match (vardecl Unit Unit))
    )
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
        (nonrec)
        (datatypebind
          (datatype
            (tyvardecl Tuple3 (fun (type) (fun (type) (fun (type) (type)))))
            (tyvardecl a (type)) (tyvardecl b (type)) (tyvardecl c (type))
            Tuple3_match
            (vardecl Tuple3 (fun a (fun b (fun c [[[Tuple3 a] b] c]))))
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
          (let
            (rec)
            (datatypebind
              (datatype
                (tyvardecl List (fun (type) (type)))
                (tyvardecl a (type))
                Nil_match
                (vardecl Nil [List a])
                (vardecl Cons (fun a (fun [List a] [List a])))
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
                (let
                  (nonrec)
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
                  (let
                    (nonrec)
                    (datatypebind
                      (datatype
                        (tyvardecl UpperBound (fun (type) (type)))
                        (tyvardecl a (type))
                        UpperBound_match
                        (vardecl
                          UpperBound
                          (fun [Extended a] (fun Bool [UpperBound a]))
                        )
                      )
                    )
                    (let
                      (nonrec)
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
                      (let
                        (nonrec)
                        (datatypebind
                          (datatype
                            (tyvardecl Maybe (fun (type) (type)))
                            (tyvardecl a (type))
                            Maybe_match
                            (vardecl Just (fun a [Maybe a]))
                            (vardecl Nothing [Maybe a])
                          )
                        )
                        (let
                          (nonrec)
                          (datatypebind
                            (datatype
                              (tyvardecl PendingTxOutRef (type))
                              
                              PendingTxOutRef_match
                              (vardecl
                                PendingTxOutRef
                                (fun (con bytestring) (fun (con integer) PendingTxOutRef))
                              )
                            )
                          )
                          (let
                            (nonrec)
                            (datatypebind
                              (datatype
                                (tyvardecl PendingTxIn (fun (type) (type)))
                                (tyvardecl w (type))
                                PendingTxIn_match
                                (vardecl
                                  PendingTxIn
                                  (fun PendingTxOutRef (fun w (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] [PendingTxIn w])))
                                )
                              )
                            )
                            (let
                              (nonrec)
                              (datatypebind
                                (datatype
                                  (tyvardecl PendingTxOutType (type))
                                  
                                  PendingTxOutType_match
                                  (vardecl
                                    PubKeyTxOut
                                    (fun (con bytestring) PendingTxOutType)
                                  )
                                  (vardecl
                                    ScriptTxOut
                                    (fun (con bytestring) (fun (con bytestring) PendingTxOutType))
                                  )
                                )
                              )
                              (let
                                (nonrec)
                                (datatypebind
                                  (datatype
                                    (tyvardecl PendingTxOut (type))
                                    
                                    PendingTxOut_match
                                    (vardecl
                                      PendingTxOut
                                      (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun PendingTxOutType PendingTxOut))
                                    )
                                  )
                                )
                                (let
                                  (nonrec)
                                  (datatypebind
                                    (datatype
                                      (tyvardecl PendingTx (fun (type) (type)))
                                      (tyvardecl i (type))
                                      PendingTx_match
                                      (vardecl
                                        PendingTx
                                        (fun [List [PendingTxIn [Maybe [[[Tuple3 (con bytestring)] (con bytestring)] (con bytestring)]]]] (fun [List PendingTxOut] (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun i (fun [Interval (con integer)] (fun [List (con bytestring)] (fun [List (con bytestring)] (fun [List [[Tuple2 (con bytestring)] Data]] (fun (con bytestring) [PendingTx i]))))))))))
                                      )
                                    )
                                  )
                                  (let
                                    (nonrec)
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
                                              (all a (type) (fun a (fun a a)))
                                              [ [ { b Bool } True ] False ]
                                            )
                                            [
                                              [ (builtin equalsByteString) arg ]
                                              arg
                                            ]
                                          ]
                                        )
                                      )
                                    )
                                    (let
                                      (nonrec)
                                      (termbind
                                        (strict)
                                        (vardecl
                                          find
                                          (all a (type) (fun (fun a Bool) (fun [List a] [Maybe a])))
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
                                                (vardecl
                                                  go (fun [List a] [Maybe a])
                                                )
                                                (lam
                                                  l
                                                  [List a]
                                                  [
                                                    [
                                                      [
                                                        {
                                                          [ { Nil_match a } l ]
                                                          (fun Unit [Maybe a])
                                                        }
                                                        (lam
                                                          thunk
                                                          Unit
                                                          { Nothing a }
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
                                                                [
                                                                  {
                                                                    [
                                                                      Bool_match
                                                                      [ p x ]
                                                                    ]
                                                                    (fun Unit [Maybe a])
                                                                  }
                                                                  (lam
                                                                    thunk
                                                                    Unit
                                                                    [
                                                                      { Just a }
                                                                      x
                                                                    ]
                                                                  )
                                                                ]
                                                                (lam
                                                                  thunk
                                                                  Unit
                                                                  [ go xs ]
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
                                              go
                                            )
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
                                                    [
                                                      [
                                                        [
                                                          {
                                                            [
                                                              { Nil_match a } l
                                                            ]
                                                            (fun Unit b)
                                                          }
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
                                                                [
                                                                  [
                                                                    [
                                                                      {
                                                                        {
                                                                          foldr
                                                                          a
                                                                        }
                                                                        b
                                                                      }
                                                                      f
                                                                    ]
                                                                    acc
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
                                        (let
                                          (nonrec)
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
                                                    (all a (type) (fun a (fun a a)))
                                                    [
                                                      [ { b Bool } True ] False
                                                    ]
                                                  )
                                                  [
                                                    [
                                                      (builtin
                                                        greaterThanEqualsInteger
                                                      )
                                                      arg
                                                    ]
                                                    arg
                                                  ]
                                                ]
                                              )
                                            )
                                          )
                                          (let
                                            (nonrec)
                                            (termbind
                                              (strict)
                                              (vardecl
                                                addInteger
                                                (fun (con integer) (fun (con integer) (con integer)))
                                              )
                                              (builtin addInteger)
                                            )
                                            (let
                                              (nonrec)
                                              (termbind
                                                (strict)
                                                (vardecl
                                                  length
                                                  (all a (type) (fun [List a] (con integer)))
                                                )
                                                (abs
                                                  a
                                                  (type)
                                                  [
                                                    [
                                                      {
                                                        { foldr a }
                                                        (con integer)
                                                      }
                                                      (lam
                                                        ds
                                                        a
                                                        (lam
                                                          acc
                                                          (con integer)
                                                          [
                                                            [ addInteger acc ]
                                                            (con 1)
                                                          ]
                                                        )
                                                      )
                                                    ]
                                                    (con 0)
                                                  ]
                                                )
                                              )
                                              (let
                                                (nonrec)
                                                (termbind
                                                  (strict)
                                                  (vardecl
                                                    trace
                                                    (fun (con string) Unit)
                                                  )
                                                  (lam
                                                    arg
                                                    (con string)
                                                    [
                                                      (lam
                                                        b
                                                        (all a (type) (fun a a))
                                                        Unit
                                                      )
                                                      [ (builtin trace) arg ]
                                                    ]
                                                  )
                                                )
                                                (let
                                                  (nonrec)
                                                  (termbind
                                                    (strict)
                                                    (vardecl
                                                      appendString
                                                      (fun (con string) (fun (con string) (con string)))
                                                    )
                                                    (builtin append)
                                                  )
                                                  (let
                                                    (nonrec)
                                                    (termbind
                                                      (strict)
                                                      (vardecl
                                                        charToString
                                                        (fun (con integer) (con string))
                                                      )
                                                      (builtin charToString)
                                                    )
                                                    (let
                                                      (nonrec)
                                                      (termbind
                                                        (strict)
                                                        (vardecl
                                                          emptyString
                                                          (con string)
                                                        )
                                                        (con )
                                                      )
                                                      (let
                                                        (rec)
                                                        (termbind
                                                          (strict)
                                                          (vardecl
                                                            toPlutusString
                                                            (fun [List (con integer)] (con string))
                                                          )
                                                          (lam
                                                            str
                                                            [List (con integer)]
                                                            [
                                                              [
                                                                [
                                                                  {
                                                                    [
                                                                      {
                                                                        Nil_match
                                                                        (con integer)
                                                                      }
                                                                      str
                                                                    ]
                                                                    (fun Unit (con string))
                                                                  }
                                                                  (lam
                                                                    thunk
                                                                    Unit
                                                                    emptyString
                                                                  )
                                                                ]
                                                                (lam
                                                                  c
                                                                  (con integer)
                                                                  (lam
                                                                    rest
                                                                    [List (con integer)]
                                                                    (lam
                                                                      thunk
                                                                      Unit
                                                                      [
                                                                        [
                                                                          appendString
                                                                          [
                                                                            charToString
                                                                            c
                                                                          ]
                                                                        ]
                                                                        [
                                                                          toPlutusString
                                                                          rest
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
                                                        (let
                                                          (nonrec)
                                                          (termbind
                                                            (nonstrict)
                                                            (vardecl
                                                              validate
                                                              [List (con integer)]
                                                            )
                                                            [
                                                              [
                                                                {
                                                                  Cons
                                                                  (con integer)
                                                                }
                                                                (con 110)
                                                              ]
                                                              [
                                                                [
                                                                  {
                                                                    Cons
                                                                    (con integer)
                                                                  }
                                                                  (con 111)
                                                                ]
                                                                [
                                                                  [
                                                                    {
                                                                      Cons
                                                                      (con integer)
                                                                    }
                                                                    (con 116)
                                                                  ]
                                                                  [
                                                                    [
                                                                      {
                                                                        Cons
                                                                        (con integer)
                                                                      }
                                                                      (con 32)
                                                                    ]
                                                                    [
                                                                      [
                                                                        {
                                                                          Cons
                                                                          (con integer)
                                                                        }
                                                                        (con 101
                                                                        )
                                                                      ]
                                                                      [
                                                                        [
                                                                          {
                                                                            Cons
                                                                            (con integer)
                                                                          }
                                                                          (con
                                                                            110
                                                                          )
                                                                        ]
                                                                        [
                                                                          [
                                                                            {
                                                                              Cons
                                                                              (con integer)
                                                                            }
                                                                            (con
                                                                              111
                                                                            )
                                                                          ]
                                                                          [
                                                                            [
                                                                              {
                                                                                Cons
                                                                                (con integer)
                                                                              }
                                                                              (con
                                                                                117
                                                                              )
                                                                            ]
                                                                            [
                                                                              [
                                                                                {
                                                                                  Cons
                                                                                  (con integer)
                                                                                }
                                                                                (con
                                                                                  103
                                                                                )
                                                                              ]
                                                                              [
                                                                                [
                                                                                  {
                                                                                    Cons
                                                                                    (con integer)
                                                                                  }
                                                                                  (con
                                                                                    104
                                                                                  )
                                                                                ]
                                                                                [
                                                                                  [
                                                                                    {
                                                                                      Cons
                                                                                      (con integer)
                                                                                    }
                                                                                    (con
                                                                                      32
                                                                                    )
                                                                                  ]
                                                                                  [
                                                                                    [
                                                                                      {
                                                                                        Cons
                                                                                        (con integer)
                                                                                      }
                                                                                      (con
                                                                                        115
                                                                                      )
                                                                                    ]
                                                                                    [
                                                                                      [
                                                                                        {
                                                                                          Cons
                                                                                          (con integer)
                                                                                        }
                                                                                        (con
                                                                                          105
                                                                                        )
                                                                                      ]
                                                                                      [
                                                                                        [
                                                                                          {
                                                                                            Cons
                                                                                            (con integer)
                                                                                          }
                                                                                          (con
                                                                                            103
                                                                                          )
                                                                                        ]
                                                                                        [
                                                                                          [
                                                                                            {
                                                                                              Cons
                                                                                              (con integer)
                                                                                            }
                                                                                            (con
                                                                                              110
                                                                                            )
                                                                                          ]
                                                                                          [
                                                                                            [
                                                                                              {
                                                                                                Cons
                                                                                                (con integer)
                                                                                              }
                                                                                              (con
                                                                                                97
                                                                                              )
                                                                                            ]
                                                                                            [
                                                                                              [
                                                                                                {
                                                                                                  Cons
                                                                                                  (con integer)
                                                                                                }
                                                                                                (con
                                                                                                  116
                                                                                                )
                                                                                              ]
                                                                                              [
                                                                                                [
                                                                                                  {
                                                                                                    Cons
                                                                                                    (con integer)
                                                                                                  }
                                                                                                  (con
                                                                                                    117
                                                                                                  )
                                                                                                ]
                                                                                                [
                                                                                                  [
                                                                                                    {
                                                                                                      Cons
                                                                                                      (con integer)
                                                                                                    }
                                                                                                    (con
                                                                                                      114
                                                                                                    )
                                                                                                  ]
                                                                                                  [
                                                                                                    [
                                                                                                      {
                                                                                                        Cons
                                                                                                        (con integer)
                                                                                                      }
                                                                                                      (con
                                                                                                        101
                                                                                                      )
                                                                                                    ]
                                                                                                    [
                                                                                                      [
                                                                                                        {
                                                                                                          Cons
                                                                                                          (con integer)
                                                                                                        }
                                                                                                        (con
                                                                                                          115
                                                                                                        )
                                                                                                      ]
                                                                                                      {
                                                                                                        Nil
                                                                                                        (con integer)
                                                                                                      }
                                                                                                    ]
                                                                                                  ]
                                                                                                ]
                                                                                              ]
                                                                                            ]
                                                                                          ]
                                                                                        ]
                                                                                      ]
                                                                                    ]
                                                                                  ]
                                                                                ]
                                                                              ]
                                                                            ]
                                                                          ]
                                                                        ]
                                                                      ]
                                                                    ]
                                                                  ]
                                                                ]
                                                              ]
                                                            ]
                                                          )
                                                          (let
                                                            (nonrec)
                                                            (termbind
                                                              (nonstrict)
                                                              (vardecl
                                                                validate
                                                                (con string)
                                                              )
                                                              [
                                                                toPlutusString
                                                                validate
                                                              ]
                                                            )
                                                            (let
                                                              (nonrec)
                                                              (termbind
                                                                (nonstrict)
                                                                (vardecl
                                                                  validate Unit
                                                                )
                                                                [
                                                                  trace validate
                                                                ]
                                                              )
                                                              (let
                                                                (nonrec)
                                                                (termbind
                                                                  (strict)
                                                                  (vardecl
                                                                    wvalidate
                                                                    (fun [List (con bytestring)] (fun (con integer) (fun [PendingTx [PendingTxIn [[[Tuple3 (con bytestring)] (con bytestring)] (con bytestring)]]] Bool)))
                                                                  )
                                                                  (lam
                                                                    ww
                                                                    [List (con bytestring)]
                                                                    (lam
                                                                      ww
                                                                      (con integer)
                                                                      (lam
                                                                        w
                                                                        [PendingTx [PendingTxIn [[[Tuple3 (con bytestring)] (con bytestring)] (con bytestring)]]]
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
                                                                                        {
                                                                                          length
                                                                                          (con bytestring)
                                                                                        }
                                                                                        [
                                                                                          [
                                                                                            [
                                                                                              {
                                                                                                {
                                                                                                  foldr
                                                                                                  (con bytestring)
                                                                                                }
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
                                                                                                      [
                                                                                                        {
                                                                                                          PendingTx_match
                                                                                                          [PendingTxIn [[[Tuple3 (con bytestring)] (con bytestring)] (con bytestring)]]
                                                                                                        }
                                                                                                        w
                                                                                                      ]
                                                                                                      [List (con bytestring)]
                                                                                                    }
                                                                                                    (lam
                                                                                                      ds
                                                                                                      [List [PendingTxIn [Maybe [[[Tuple3 (con bytestring)] (con bytestring)] (con bytestring)]]]]
                                                                                                      (lam
                                                                                                        ds
                                                                                                        [List PendingTxOut]
                                                                                                        (lam
                                                                                                          ds
                                                                                                          [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                          (lam
                                                                                                            ds
                                                                                                            [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                            (lam
                                                                                                              ds
                                                                                                              [PendingTxIn [[[Tuple3 (con bytestring)] (con bytestring)] (con bytestring)]]
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
                                                                                                    )
                                                                                                  ]
                                                                                                )
                                                                                              )
                                                                                            ]
                                                                                            {
                                                                                              Nil
                                                                                              (con bytestring)
                                                                                            }
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
                                                                              (lam
                                                                                thunk
                                                                                Unit
                                                                                True
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
                                                                                      validate
                                                                                    ]
                                                                                    (fun Unit Bool)
                                                                                  }
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
                                                                  )
                                                                )
                                                                (let
                                                                  (nonrec)
                                                                  (datatypebind
                                                                    (datatype
                                                                      (tyvardecl
                                                                        MultiSig
                                                                        (type)
                                                                      )
                                                                      
                                                                      MultiSig_match
                                                                      (vardecl
                                                                        MultiSig
                                                                        (fun [List (con bytestring)] (fun (con integer) MultiSig))
                                                                      )
                                                                    )
                                                                  )
                                                                  (let
                                                                    (nonrec)
                                                                    (termbind
                                                                      (strict)
                                                                      (vardecl
                                                                        validate
                                                                        (fun MultiSig (fun Unit (fun Unit (fun [PendingTx [PendingTxIn [[[Tuple3 (con bytestring)] (con bytestring)] (con bytestring)]]] Bool))))
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
                                                                              [PendingTx [PendingTxIn [[[Tuple3 (con bytestring)] (con bytestring)] (con bytestring)]]]
                                                                              [
                                                                                {
                                                                                  [
                                                                                    MultiSig_match
                                                                                    w
                                                                                  ]
                                                                                  Bool
                                                                                }
                                                                                (lam
                                                                                  ww
                                                                                  [List (con bytestring)]
                                                                                  (lam
                                                                                    ww
                                                                                    (con integer)
                                                                                    [
                                                                                      [
                                                                                        [
                                                                                          wvalidate
                                                                                          ww
                                                                                        ]
                                                                                        ww
                                                                                      ]
                                                                                      w
                                                                                    ]
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