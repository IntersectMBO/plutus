(program
  (let
    (nonrec)
    (datatypebind
      (datatype (tyvardecl Unit (type))  Unit_match (vardecl Unit Unit))
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
          (datatypebind
            (datatype
              (tyvardecl Bool (type))
              
              Bool_match
              (vardecl True Bool) (vardecl False Bool)
            )
          )
          (let
            (nonrec)
            (datatypebind
              (datatype
                (tyvardecl Ordering (type))
                
                Ordering_match
                (vardecl EQ Ordering)
                (vardecl GT Ordering)
                (vardecl LT Ordering)
              )
            )
            (let
              (nonrec)
              (termbind
                (strict)
                (vardecl
                  equalsInteger (fun (con integer) (fun (con integer) Bool))
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
                        [ [ { b Bool } True ] False ]
                      )
                      [ [ (builtin equalsInteger) arg ] arg ]
                    ]
                  )
                )
              )
              (let
                (nonrec)
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
                          (all a (type) (fun a (fun a a)))
                          [ [ { b Bool } True ] False ]
                        )
                        [ [ (builtin lessThanEqualsInteger) arg ] arg ]
                      ]
                    )
                  )
                )
                (let
                  (nonrec)
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
                        [
                          [
                            [
                              {
                                [ Bool_match [ [ equalsInteger x ] y ] ]
                                (fun Unit Ordering)
                              }
                              (lam thunk Unit EQ)
                            ]
                            (lam
                              thunk
                              Unit
                              [
                                [
                                  [
                                    {
                                      [
                                        Bool_match [ [ lessThanEqInteger x ] y ]
                                      ]
                                      (fun Unit Ordering)
                                    }
                                    (lam thunk Unit LT)
                                  ]
                                  (lam thunk Unit GT)
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
                  (let
                    (nonrec)
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
                          [
                            [
                              [
                                {
                                  [ Bool_match [ [ lessThanEqInteger x ] y ] ]
                                  (fun Unit (con integer))
                                }
                                (lam thunk Unit y)
                              ]
                              (lam thunk Unit x)
                            ]
                            Unit
                          ]
                        )
                      )
                    )
                    (let
                      (nonrec)
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
                            [
                              [
                                [
                                  {
                                    [ Bool_match [ [ lessThanEqInteger x ] y ] ]
                                    (fun Unit (con integer))
                                  }
                                  (lam thunk Unit x)
                                ]
                                (lam thunk Unit y)
                              ]
                              Unit
                            ]
                          )
                        )
                      )
                      (let
                        (nonrec)
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
                                    [ [ { b Bool } True ] False ]
                                  )
                                  [
                                    [ (builtin greaterThanEqualsInteger) arg ]
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
                                      (all a (type) (fun a (fun a a)))
                                      [ [ { b Bool } True ] False ]
                                    )
                                    [ [ (builtin greaterThanInteger) arg ] arg ]
                                  ]
                                )
                              )
                            )
                            (let
                              (nonrec)
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
                                        (all a (type) (fun a (fun a a)))
                                        [ [ { b Bool } True ] False ]
                                      )
                                      [ [ (builtin lessThanInteger) arg ] arg ]
                                    ]
                                  )
                                )
                              )
                              (let
                                (nonrec)
                                (termbind
                                  (nonstrict)
                                  (vardecl fOrdSlot [Ord (con integer)])
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
                                (let
                                  (nonrec)
                                  (termbind
                                    (strict)
                                    (vardecl
                                      bad_name
                                      (all a (type) (fun [Ord a] (fun a (fun a Bool))))
                                    )
                                    (abs
                                      a
                                      (type)
                                      (lam
                                        v
                                        [Ord a]
                                        [
                                          {
                                            [ { Ord_match a } v ]
                                            (fun a (fun a Bool))
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
                                                        (lam
                                                          v (fun a (fun a a)) v
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
                                  (let
                                    (nonrec)
                                    (termbind
                                      (strict)
                                      (vardecl
                                        bad_name
                                        (all a (type) (fun [Ord a] (fun a (fun a Bool))))
                                      )
                                      (abs
                                        a
                                        (type)
                                        (lam
                                          v
                                          [Ord a]
                                          [
                                            {
                                              [ { Ord_match a } v ]
                                              (fun a (fun a Bool))
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
                                                          (lam
                                                            v
                                                            (fun a (fun a a))
                                                            v
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
                                        (termbind
                                          (strict)
                                          (vardecl
                                            wcontains
                                            (all a (type) (fun [Ord a] (fun [Maybe a] (fun [Maybe a] (fun [Maybe a] (fun [Maybe a] Bool))))))
                                          )
                                          (abs
                                            a
                                            (type)
                                            (lam
                                              w
                                              [Ord a]
                                              (lam
                                                ww
                                                [Maybe a]
                                                (lam
                                                  ww
                                                  [Maybe a]
                                                  (lam
                                                    ww
                                                    [Maybe a]
                                                    (lam
                                                      ww
                                                      [Maybe a]
                                                      (let
                                                        (nonrec)
                                                        (termbind
                                                          (nonstrict)
                                                          (vardecl j Bool)
                                                          [
                                                            [
                                                              [
                                                                {
                                                                  [
                                                                    {
                                                                      Maybe_match
                                                                      a
                                                                    }
                                                                    ww
                                                                  ]
                                                                  (fun Unit Bool)
                                                                }
                                                                (lam
                                                                  at
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
                                                                                a
                                                                              }
                                                                              ww
                                                                            ]
                                                                            (fun Unit Bool)
                                                                          }
                                                                          (lam
                                                                            bt
                                                                            a
                                                                            (lam
                                                                              thunk
                                                                              Unit
                                                                              [
                                                                                [
                                                                                  [
                                                                                    {
                                                                                      bad_name
                                                                                      a
                                                                                    }
                                                                                    w
                                                                                  ]
                                                                                  at
                                                                                ]
                                                                                bt
                                                                              ]
                                                                            )
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
                                                                thunk Unit True
                                                              )
                                                            ]
                                                            Unit
                                                          ]
                                                        )
                                                        [
                                                          [
                                                            [
                                                              {
                                                                [
                                                                  {
                                                                    Maybe_match
                                                                    a
                                                                  }
                                                                  ww
                                                                ]
                                                                (fun Unit Bool)
                                                              }
                                                              (lam
                                                                af
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
                                                                              a
                                                                            }
                                                                            ww
                                                                          ]
                                                                          (fun Unit Bool)
                                                                        }
                                                                        (lam
                                                                          bf
                                                                          a
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
                                                                                            {
                                                                                              bad_name
                                                                                              a
                                                                                            }
                                                                                            w
                                                                                          ]
                                                                                          af
                                                                                        ]
                                                                                        bf
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
                                                                                  False
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
                                                                        False
                                                                      )
                                                                    ]
                                                                    Unit
                                                                  ]
                                                                )
                                                              )
                                                            ]
                                                            (lam thunk Unit j)
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
                                        (let
                                          (nonrec)
                                          (datatypebind
                                            (datatype
                                              (tyvardecl
                                                Tuple2
                                                (fun (type) (fun (type) (type)))
                                              )
                                              (tyvardecl a (type))
                                              (tyvardecl b (type))
                                              Tuple2_match
                                              (vardecl
                                                Tuple2
                                                (fun a (fun b [[Tuple2 a] b]))
                                              )
                                            )
                                          )
                                          (let
                                            (nonrec)
                                            (datatypebind
                                              (datatype
                                                (tyvardecl
                                                  PendingTxOutType (type)
                                                )
                                                
                                                PendingTxOutType_match
                                                (vardecl
                                                  DataTxOut PendingTxOutType
                                                )
                                                (vardecl
                                                  PubKeyTxOut
                                                  (fun (con bytestring) PendingTxOutType)
                                                )
                                              )
                                            )
                                            (let
                                              (nonrec)
                                              (datatypebind
                                                (datatype
                                                  (tyvardecl PendingTxOut (type)
                                                  )
                                                  
                                                  PendingTxOut_match
                                                  (vardecl
                                                    PendingTxOut
                                                    (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun [Maybe [[Tuple2 (con bytestring)] (con bytestring)]] (fun PendingTxOutType PendingTxOut)))
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
                                                          [
                                                            [ { b Bool } True ]
                                                            False
                                                          ]
                                                        )
                                                        [
                                                          [
                                                            (builtin
                                                              equalsByteString
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
                                                                        {
                                                                          Nil_match
                                                                          a
                                                                        }
                                                                        l
                                                                      ]
                                                                      (fun Unit b)
                                                                    }
                                                                    (lam
                                                                      thunk
                                                                      Unit
                                                                      acc
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
                                                                            f x
                                                                          ]
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
                                                        wgetContinuingOutputs
                                                        (fun [List PendingTxOut] (fun [Maybe [[Tuple2 (con bytestring)] (con bytestring)]] [List PendingTxOut]))
                                                      )
                                                      (lam
                                                        ww
                                                        [List PendingTxOut]
                                                        (lam
                                                          ww
                                                          [Maybe [[Tuple2 (con bytestring)] (con bytestring)]]
                                                          [
                                                            [
                                                              [
                                                                {
                                                                  [
                                                                    {
                                                                      Maybe_match
                                                                      [[Tuple2 (con bytestring)] (con bytestring)]
                                                                    }
                                                                    ww
                                                                  ]
                                                                  (fun Unit [List PendingTxOut])
                                                                }
                                                                (lam
                                                                  ds
                                                                  [[Tuple2 (con bytestring)] (con bytestring)]
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
                                                                            (con bytestring)
                                                                          }
                                                                          ds
                                                                        ]
                                                                        [List PendingTxOut]
                                                                      }
                                                                      (lam
                                                                        inpHsh
                                                                        (con bytestring)
                                                                        (lam
                                                                          ds
                                                                          (con bytestring)
                                                                          [
                                                                            [
                                                                              [
                                                                                {
                                                                                  {
                                                                                    foldr
                                                                                    PendingTxOut
                                                                                  }
                                                                                  [List PendingTxOut]
                                                                                }
                                                                                (lam
                                                                                  e
                                                                                  PendingTxOut
                                                                                  (lam
                                                                                    xs
                                                                                    [List PendingTxOut]
                                                                                    (let
                                                                                      (nonrec
                                                                                      )
                                                                                      (termbind
                                                                                        (strict
                                                                                        )
                                                                                        (vardecl
                                                                                          wild
                                                                                          PendingTxOut
                                                                                        )
                                                                                        e
                                                                                      )
                                                                                      [
                                                                                        {
                                                                                          [
                                                                                            PendingTxOut_match
                                                                                            e
                                                                                          ]
                                                                                          [List PendingTxOut]
                                                                                        }
                                                                                        (lam
                                                                                          ds
                                                                                          [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                          (lam
                                                                                            ds
                                                                                            [Maybe [[Tuple2 (con bytestring)] (con bytestring)]]
                                                                                            (lam
                                                                                              ds
                                                                                              PendingTxOutType
                                                                                              [
                                                                                                [
                                                                                                  [
                                                                                                    {
                                                                                                      [
                                                                                                        {
                                                                                                          Maybe_match
                                                                                                          [[Tuple2 (con bytestring)] (con bytestring)]
                                                                                                        }
                                                                                                        ds
                                                                                                      ]
                                                                                                      (fun Unit [List PendingTxOut])
                                                                                                    }
                                                                                                    (lam
                                                                                                      ds
                                                                                                      [[Tuple2 (con bytestring)] (con bytestring)]
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
                                                                                                                (con bytestring)
                                                                                                              }
                                                                                                              ds
                                                                                                            ]
                                                                                                            [List PendingTxOut]
                                                                                                          }
                                                                                                          (lam
                                                                                                            outHsh
                                                                                                            (con bytestring)
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
                                                                                                                            equalsByteString
                                                                                                                            outHsh
                                                                                                                          ]
                                                                                                                          inpHsh
                                                                                                                        ]
                                                                                                                      ]
                                                                                                                      (fun Unit [List PendingTxOut])
                                                                                                                    }
                                                                                                                    (lam
                                                                                                                      thunk
                                                                                                                      Unit
                                                                                                                      [
                                                                                                                        [
                                                                                                                          {
                                                                                                                            Cons
                                                                                                                            PendingTxOut
                                                                                                                          }
                                                                                                                          wild
                                                                                                                        ]
                                                                                                                        xs
                                                                                                                      ]
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
                                                                                      ]
                                                                                    )
                                                                                  )
                                                                                )
                                                                              ]
                                                                              {
                                                                                Nil
                                                                                PendingTxOut
                                                                              }
                                                                            ]
                                                                            ww
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
                                                                {
                                                                  Nil
                                                                  PendingTxOut
                                                                }
                                                              )
                                                            ]
                                                            Unit
                                                          ]
                                                        )
                                                      )
                                                    )
                                                    (let
                                                      (nonrec)
                                                      (termbind
                                                        (strict)
                                                        (vardecl
                                                          wscriptOutputsAt
                                                          (fun (con bytestring) (fun [List PendingTxOut] [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]]))
                                                        )
                                                        (lam
                                                          w
                                                          (con bytestring)
                                                          (lam
                                                            ww
                                                            [List PendingTxOut]
                                                            [
                                                              [
                                                                [
                                                                  {
                                                                    {
                                                                      foldr
                                                                      PendingTxOut
                                                                    }
                                                                    [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]]
                                                                  }
                                                                  (lam
                                                                    e
                                                                    PendingTxOut
                                                                    (lam
                                                                      xs
                                                                      [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]]
                                                                      [
                                                                        {
                                                                          [
                                                                            PendingTxOut_match
                                                                            e
                                                                          ]
                                                                          [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]]
                                                                        }
                                                                        (lam
                                                                          ds
                                                                          [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                          (lam
                                                                            ds
                                                                            [Maybe [[Tuple2 (con bytestring)] (con bytestring)]]
                                                                            (lam
                                                                              ds
                                                                              PendingTxOutType
                                                                              [
                                                                                [
                                                                                  [
                                                                                    {
                                                                                      [
                                                                                        {
                                                                                          Maybe_match
                                                                                          [[Tuple2 (con bytestring)] (con bytestring)]
                                                                                        }
                                                                                        ds
                                                                                      ]
                                                                                      (fun Unit [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]])
                                                                                    }
                                                                                    (lam
                                                                                      ds
                                                                                      [[Tuple2 (con bytestring)] (con bytestring)]
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
                                                                                                (con bytestring)
                                                                                              }
                                                                                              ds
                                                                                            ]
                                                                                            [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]]
                                                                                          }
                                                                                          (lam
                                                                                            h
                                                                                            (con bytestring)
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
                                                                                                            equalsByteString
                                                                                                            w
                                                                                                          ]
                                                                                                          h
                                                                                                        ]
                                                                                                      ]
                                                                                                      (fun Unit [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]])
                                                                                                    }
                                                                                                    (lam
                                                                                                      thunk
                                                                                                      Unit
                                                                                                      [
                                                                                                        [
                                                                                                          {
                                                                                                            Cons
                                                                                                            [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                                                                          }
                                                                                                          [
                                                                                                            [
                                                                                                              {
                                                                                                                {
                                                                                                                  Tuple2
                                                                                                                  (con bytestring)
                                                                                                                }
                                                                                                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                              }
                                                                                                              ds
                                                                                                            ]
                                                                                                            ds
                                                                                                          ]
                                                                                                        ]
                                                                                                        xs
                                                                                                      ]
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
                                                                      ]
                                                                    )
                                                                  )
                                                                ]
                                                                {
                                                                  Nil
                                                                  [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                                }
                                                              ]
                                                              ww
                                                            ]
                                                          )
                                                        )
                                                      )
                                                      (let
                                                        (nonrec)
                                                        (datatypebind
                                                          (datatype
                                                            (tyvardecl
                                                              Interval
                                                              (fun (type) (type))
                                                            )
                                                            (tyvardecl a (type))
                                                            Interval_match
                                                            (vardecl
                                                              Interval
                                                              (fun [Maybe a] (fun [Maybe a] [Interval a]))
                                                            )
                                                          )
                                                        )
                                                        (let
                                                          (nonrec)
                                                          (datatypebind
                                                            (datatype
                                                              (tyvardecl
                                                                PendingTxOutRef
                                                                (type)
                                                              )
                                                              
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
                                                                (tyvardecl
                                                                  PendingTxIn
                                                                  (type)
                                                                )
                                                                
                                                                PendingTxIn_match
                                                                (vardecl
                                                                  PendingTxIn
                                                                  (fun PendingTxOutRef (fun [Maybe [[Tuple2 (con bytestring)] (con bytestring)]] (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] PendingTxIn)))
                                                                )
                                                              )
                                                            )
                                                            (let
                                                              (nonrec)
                                                              (datatypebind
                                                                (datatype
                                                                  (tyvardecl
                                                                    VestingTranche
                                                                    (type)
                                                                  )
                                                                  
                                                                  VestingTranche_match
                                                                  (vardecl
                                                                    VestingTranche
                                                                    (fun (con integer) (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] VestingTranche))
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
                                                                  (builtin
                                                                    addInteger
                                                                  )
                                                                )
                                                                (let
                                                                  (nonrec)
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
                                                                        w
                                                                        [Ord a]
                                                                        (lam
                                                                          w
                                                                          [Interval a]
                                                                          (lam
                                                                            w
                                                                            [Interval a]
                                                                            [
                                                                              {
                                                                                [
                                                                                  {
                                                                                    Interval_match
                                                                                    a
                                                                                  }
                                                                                  w
                                                                                ]
                                                                                Bool
                                                                              }
                                                                              (lam
                                                                                ww
                                                                                [Maybe a]
                                                                                (lam
                                                                                  ww
                                                                                  [Maybe a]
                                                                                  [
                                                                                    {
                                                                                      [
                                                                                        {
                                                                                          Interval_match
                                                                                          a
                                                                                        }
                                                                                        w
                                                                                      ]
                                                                                      Bool
                                                                                    }
                                                                                    (lam
                                                                                      ww
                                                                                      [Maybe a]
                                                                                      (lam
                                                                                        ww
                                                                                        [Maybe a]
                                                                                        [
                                                                                          [
                                                                                            [
                                                                                              [
                                                                                                [
                                                                                                  {
                                                                                                    wcontains
                                                                                                    a
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
                                                                  (let
                                                                    (nonrec)
                                                                    (termbind
                                                                      (strict)
                                                                      (vardecl
                                                                        availableFrom
                                                                        (fun VestingTranche (fun [Interval (con integer)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]))
                                                                      )
                                                                      (lam
                                                                        ds
                                                                        VestingTranche
                                                                        (lam
                                                                          range
                                                                          [Interval (con integer)]
                                                                          [
                                                                            {
                                                                              [
                                                                                VestingTranche_match
                                                                                ds
                                                                              ]
                                                                              [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                            }
                                                                            (lam
                                                                              d
                                                                              (con integer)
                                                                              (lam
                                                                                v
                                                                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
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
                                                                                                  contains
                                                                                                  (con integer)
                                                                                                }
                                                                                                fOrdSlot
                                                                                              ]
                                                                                              [
                                                                                                [
                                                                                                  {
                                                                                                    Interval
                                                                                                    (con integer)
                                                                                                  }
                                                                                                  [
                                                                                                    {
                                                                                                      Just
                                                                                                      (con integer)
                                                                                                    }
                                                                                                    d
                                                                                                  ]
                                                                                                ]
                                                                                                {
                                                                                                  Nothing
                                                                                                  (con integer)
                                                                                                }
                                                                                              ]
                                                                                            ]
                                                                                            range
                                                                                          ]
                                                                                        ]
                                                                                        (fun Unit [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]])
                                                                                      }
                                                                                      (lam
                                                                                        thunk
                                                                                        Unit
                                                                                        v
                                                                                      )
                                                                                    ]
                                                                                    (lam
                                                                                      thunk
                                                                                      Unit
                                                                                      {
                                                                                        Nil
                                                                                        [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
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
                                                                    )
                                                                    (let
                                                                      (nonrec)
                                                                      (datatypebind
                                                                        (datatype
                                                                          (tyvardecl
                                                                            These
                                                                            (fun (type) (fun (type) (type)))
                                                                          )
                                                                          (tyvardecl
                                                                            a
                                                                            (type)
                                                                          )
                                                                          (tyvardecl
                                                                            b
                                                                            (type)
                                                                          )
                                                                          These_match
                                                                          (vardecl
                                                                            That
                                                                            (fun b [[These a] b])
                                                                          )
                                                                          (vardecl
                                                                            These
                                                                            (fun a (fun b [[These a] b]))
                                                                          )
                                                                          (vardecl
                                                                            This
                                                                            (fun a [[These a] b])
                                                                          )
                                                                        )
                                                                      )
                                                                      (let
                                                                        (nonrec)
                                                                        (termbind
                                                                          (strict
                                                                          )
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
                                                                                                foldr
                                                                                                [[Tuple2 k] [[These v] r]]
                                                                                              }
                                                                                              [List [[Tuple2 k] [[These v] r]]]
                                                                                            }
                                                                                            {
                                                                                              Cons
                                                                                              [[Tuple2 k] [[These v] r]]
                                                                                            }
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
                                                                                                      {
                                                                                                        {
                                                                                                          Tuple2_match
                                                                                                          k
                                                                                                        }
                                                                                                        r
                                                                                                      }
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
                                                                                                            {
                                                                                                              Tuple2
                                                                                                              k
                                                                                                            }
                                                                                                            [[These v] r]
                                                                                                          }
                                                                                                          c
                                                                                                        ]
                                                                                                        [
                                                                                                          {
                                                                                                            {
                                                                                                              That
                                                                                                              v
                                                                                                            }
                                                                                                            r
                                                                                                          }
                                                                                                          b
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
                                                                                                      foldr
                                                                                                      [[Tuple2 k] r]
                                                                                                    }
                                                                                                    [List [[Tuple2 k] r]]
                                                                                                  }
                                                                                                  (lam
                                                                                                    e
                                                                                                    [[Tuple2 k] r]
                                                                                                    (lam
                                                                                                      xs
                                                                                                      [List [[Tuple2 k] r]]
                                                                                                      (let
                                                                                                        (nonrec
                                                                                                        )
                                                                                                        (termbind
                                                                                                          (strict
                                                                                                          )
                                                                                                          (vardecl
                                                                                                            wild
                                                                                                            [[Tuple2 k] r]
                                                                                                          )
                                                                                                          e
                                                                                                        )
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
                                                                                                                                  foldr
                                                                                                                                  [[Tuple2 k] v]
                                                                                                                                }
                                                                                                                                Bool
                                                                                                                              }
                                                                                                                              (lam
                                                                                                                                a
                                                                                                                                [[Tuple2 k] v]
                                                                                                                                (lam
                                                                                                                                  acc
                                                                                                                                  Bool
                                                                                                                                  [
                                                                                                                                    [
                                                                                                                                      [
                                                                                                                                        {
                                                                                                                                          [
                                                                                                                                            Bool_match
                                                                                                                                            acc
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
                                                                                                                                          {
                                                                                                                                            [
                                                                                                                                              {
                                                                                                                                                {
                                                                                                                                                  Tuple2_match
                                                                                                                                                  k
                                                                                                                                                }
                                                                                                                                                v
                                                                                                                                              }
                                                                                                                                              a
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
                                                                                                                                    Unit
                                                                                                                                  ]
                                                                                                                                )
                                                                                                                              )
                                                                                                                            ]
                                                                                                                            False
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
                                                                                                                        wild
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
                                                                                                  )
                                                                                                ]
                                                                                                {
                                                                                                  Nil
                                                                                                  [[Tuple2 k] r]
                                                                                                }
                                                                                              ]
                                                                                              ds
                                                                                            ]
                                                                                          ]
                                                                                        ]
                                                                                        [
                                                                                          [
                                                                                            {
                                                                                              {
                                                                                                fFunctorNil_cfmap
                                                                                                [[Tuple2 k] v]
                                                                                              }
                                                                                              [[Tuple2 k] [[These v] r]]
                                                                                            }
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
                                                                                                  [[Tuple2 k] [[These v] r]]
                                                                                                }
                                                                                                (lam
                                                                                                  c
                                                                                                  k
                                                                                                  (lam
                                                                                                    i
                                                                                                    v
                                                                                                    [
                                                                                                      [
                                                                                                        {
                                                                                                          {
                                                                                                            Tuple2
                                                                                                            k
                                                                                                          }
                                                                                                          [[These v] r]
                                                                                                        }
                                                                                                        c
                                                                                                      ]
                                                                                                      (let
                                                                                                        (rec
                                                                                                        )
                                                                                                        (termbind
                                                                                                          (strict
                                                                                                          )
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
                                                                                                                        {
                                                                                                                          This
                                                                                                                          v
                                                                                                                        }
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
                                                                                                          go
                                                                                                          ds
                                                                                                        ]
                                                                                                      )
                                                                                                    ]
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
                                                                        (let
                                                                          (nonrec
                                                                          )
                                                                          (termbind
                                                                            (strict
                                                                            )
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
                                                                                  (rec
                                                                                  )
                                                                                  (termbind
                                                                                    (strict
                                                                                    )
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
                                                                                                                      (rec
                                                                                                                      )
                                                                                                                      (termbind
                                                                                                                        (strict
                                                                                                                        )
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
                                                                                                                      [
                                                                                                                        go
                                                                                                                        b
                                                                                                                      ]
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
                                                                                                                  (rec
                                                                                                                  )
                                                                                                                  (termbind
                                                                                                                    (strict
                                                                                                                    )
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
                                                                                                                  [
                                                                                                                    go
                                                                                                                    a
                                                                                                                  ]
                                                                                                                )
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
                                                                                    go
                                                                                    [
                                                                                      [
                                                                                        [
                                                                                          {
                                                                                            {
                                                                                              {
                                                                                                union
                                                                                                (con bytestring)
                                                                                              }
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
                                                                          (let
                                                                            (nonrec
                                                                            )
                                                                            (termbind
                                                                              (strict
                                                                              )
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
                                                                                      (rec
                                                                                      )
                                                                                      (termbind
                                                                                        (strict
                                                                                        )
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
                                                                                                (lam
                                                                                                  thunk
                                                                                                  Unit
                                                                                                  True
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
                                                                                                        Bool
                                                                                                      }
                                                                                                      (lam
                                                                                                        ds
                                                                                                        (con bytestring)
                                                                                                        (lam
                                                                                                          x
                                                                                                          [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]
                                                                                                          (let
                                                                                                            (rec
                                                                                                            )
                                                                                                            (termbind
                                                                                                              (strict
                                                                                                              )
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
                                                                                                                        [
                                                                                                                          go
                                                                                                                          xs
                                                                                                                        ]
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
                                                                                                            [
                                                                                                              go
                                                                                                              x
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
                                                                                      [
                                                                                        go
                                                                                        [
                                                                                          [
                                                                                            unionVal
                                                                                            l
                                                                                          ]
                                                                                          r
                                                                                        ]
                                                                                      ]
                                                                                    )
                                                                                  )
                                                                                )
                                                                              )
                                                                            )
                                                                            (let
                                                                              (nonrec
                                                                              )
                                                                              (termbind
                                                                                (strict
                                                                                )
                                                                                (vardecl
                                                                                  error
                                                                                  (all a (type) (fun Unit a))
                                                                                )
                                                                                (abs
                                                                                  e
                                                                                  (type)
                                                                                  (lam
                                                                                    thunk
                                                                                    Unit
                                                                                    (error
                                                                                      e
                                                                                    )
                                                                                  )
                                                                                )
                                                                              )
                                                                              (let
                                                                                (nonrec
                                                                                )
                                                                                (termbind
                                                                                  (strict
                                                                                  )
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
                                                                                            (rec
                                                                                            )
                                                                                            (termbind
                                                                                              (strict
                                                                                              )
                                                                                              (vardecl
                                                                                                go
                                                                                                (fun [List a] b)
                                                                                              )
                                                                                              (lam
                                                                                                ds
                                                                                                [List a]
                                                                                                [
                                                                                                  [
                                                                                                    [
                                                                                                      {
                                                                                                        [
                                                                                                          {
                                                                                                            Nil_match
                                                                                                            a
                                                                                                          }
                                                                                                          ds
                                                                                                        ]
                                                                                                        (fun Unit b)
                                                                                                      }
                                                                                                      (lam
                                                                                                        thunk
                                                                                                        Unit
                                                                                                        z
                                                                                                      )
                                                                                                    ]
                                                                                                    (lam
                                                                                                      y
                                                                                                      a
                                                                                                      (lam
                                                                                                        ys
                                                                                                        [List a]
                                                                                                        (lam
                                                                                                          thunk
                                                                                                          Unit
                                                                                                          [
                                                                                                            [
                                                                                                              k
                                                                                                              y
                                                                                                            ]
                                                                                                            [
                                                                                                              go
                                                                                                              ys
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
                                                                                            go
                                                                                          )
                                                                                        )
                                                                                      )
                                                                                    )
                                                                                  )
                                                                                )
                                                                                (let
                                                                                  (rec
                                                                                  )
                                                                                  (termbind
                                                                                    (strict
                                                                                    )
                                                                                    (vardecl
                                                                                      map
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
                                                                                                    [
                                                                                                      {
                                                                                                        Nil_match
                                                                                                        a
                                                                                                      }
                                                                                                      l
                                                                                                    ]
                                                                                                    (fun Unit [List b])
                                                                                                  }
                                                                                                  (lam
                                                                                                    thunk
                                                                                                    Unit
                                                                                                    {
                                                                                                      Nil
                                                                                                      b
                                                                                                    }
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
                                                                                                            Cons
                                                                                                            b
                                                                                                          }
                                                                                                          [
                                                                                                            f
                                                                                                            x
                                                                                                          ]
                                                                                                        ]
                                                                                                        [
                                                                                                          [
                                                                                                            {
                                                                                                              {
                                                                                                                map
                                                                                                                a
                                                                                                              }
                                                                                                              b
                                                                                                            }
                                                                                                            f
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
                                                                                  (let
                                                                                    (nonrec
                                                                                    )
                                                                                    (termbind
                                                                                      (strict
                                                                                      )
                                                                                      (vardecl
                                                                                        pendingTxOutValue
                                                                                        (fun PendingTxOut [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]])
                                                                                      )
                                                                                      (lam
                                                                                        ds
                                                                                        PendingTxOut
                                                                                        [
                                                                                          {
                                                                                            [
                                                                                              PendingTxOut_match
                                                                                              ds
                                                                                            ]
                                                                                            [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                          }
                                                                                          (lam
                                                                                            ds
                                                                                            [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                            (lam
                                                                                              ds
                                                                                              [Maybe [[Tuple2 (con bytestring)] (con bytestring)]]
                                                                                              (lam
                                                                                                ds
                                                                                                PendingTxOutType
                                                                                                ds
                                                                                              )
                                                                                            )
                                                                                          )
                                                                                        ]
                                                                                      )
                                                                                    )
                                                                                    (let
                                                                                      (nonrec
                                                                                      )
                                                                                      (termbind
                                                                                        (strict
                                                                                        )
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
                                                                                                (rec
                                                                                                )
                                                                                                (termbind
                                                                                                  (strict
                                                                                                  )
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
                                                                                                                          (let
                                                                                                                            (rec
                                                                                                                            )
                                                                                                                            (termbind
                                                                                                                              (strict
                                                                                                                              )
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
                                                                                                                              go
                                                                                                                              i
                                                                                                                            ]
                                                                                                                          )
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
                                                                                                  go
                                                                                                  [
                                                                                                    [
                                                                                                      unionVal
                                                                                                      ls
                                                                                                    ]
                                                                                                    rs
                                                                                                  ]
                                                                                                ]
                                                                                              )
                                                                                            )
                                                                                          )
                                                                                        )
                                                                                      )
                                                                                      (let
                                                                                        (nonrec
                                                                                        )
                                                                                        (termbind
                                                                                          (nonstrict
                                                                                          )
                                                                                          (vardecl
                                                                                            plus
                                                                                            (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]))
                                                                                          )
                                                                                          [
                                                                                            unionWith
                                                                                            addInteger
                                                                                          ]
                                                                                        )
                                                                                        (let
                                                                                          (nonrec
                                                                                          )
                                                                                          (termbind
                                                                                            (strict
                                                                                            )
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
                                                                                                    {
                                                                                                      [
                                                                                                        {
                                                                                                          {
                                                                                                            Tuple2_match
                                                                                                            a
                                                                                                          }
                                                                                                          b
                                                                                                        }
                                                                                                        ds
                                                                                                      ]
                                                                                                      b
                                                                                                    }
                                                                                                    (lam
                                                                                                      ds
                                                                                                      a
                                                                                                      (lam
                                                                                                        b
                                                                                                        b
                                                                                                        b
                                                                                                      )
                                                                                                    )
                                                                                                  ]
                                                                                                )
                                                                                              )
                                                                                            )
                                                                                          )
                                                                                          (let
                                                                                            (nonrec
                                                                                            )
                                                                                            (termbind
                                                                                              (strict
                                                                                              )
                                                                                              (vardecl
                                                                                                subtractInteger
                                                                                                (fun (con integer) (fun (con integer) (con integer)))
                                                                                              )
                                                                                              (builtin
                                                                                                subtractInteger
                                                                                              )
                                                                                            )
                                                                                            (let
                                                                                              (nonrec
                                                                                              )
                                                                                              (termbind
                                                                                                (strict
                                                                                                )
                                                                                                (vardecl
                                                                                                  wmkValidator
                                                                                                  (fun VestingTranche (fun VestingTranche (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun Unit (fun [List PendingTxOut] (fun PendingTxIn (fun [Interval (con integer)] Bool)))))))
                                                                                                )
                                                                                                (lam
                                                                                                  ww
                                                                                                  VestingTranche
                                                                                                  (lam
                                                                                                    ww
                                                                                                    VestingTranche
                                                                                                    (lam
                                                                                                      ww
                                                                                                      [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                      (lam
                                                                                                        w
                                                                                                        Unit
                                                                                                        (lam
                                                                                                          ww
                                                                                                          [List PendingTxOut]
                                                                                                          (lam
                                                                                                            ww
                                                                                                            PendingTxIn
                                                                                                            (lam
                                                                                                              ww
                                                                                                              [Interval (con integer)]
                                                                                                              (let
                                                                                                                (nonrec
                                                                                                                )
                                                                                                                (termbind
                                                                                                                  (nonstrict
                                                                                                                  )
                                                                                                                  (vardecl
                                                                                                                    newAmount
                                                                                                                    [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                  )
                                                                                                                  [
                                                                                                                    [
                                                                                                                      [
                                                                                                                        unionWith
                                                                                                                        addInteger
                                                                                                                      ]
                                                                                                                      ww
                                                                                                                    ]
                                                                                                                    [
                                                                                                                      [
                                                                                                                        [
                                                                                                                          unionWith
                                                                                                                          subtractInteger
                                                                                                                        ]
                                                                                                                        [
                                                                                                                          {
                                                                                                                            [
                                                                                                                              PendingTxIn_match
                                                                                                                              ww
                                                                                                                            ]
                                                                                                                            [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                          }
                                                                                                                          (lam
                                                                                                                            ds
                                                                                                                            PendingTxOutRef
                                                                                                                            (lam
                                                                                                                              ds
                                                                                                                              [Maybe [[Tuple2 (con bytestring)] (con bytestring)]]
                                                                                                                              (lam
                                                                                                                                ds
                                                                                                                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                                ds
                                                                                                                              )
                                                                                                                            )
                                                                                                                          )
                                                                                                                        ]
                                                                                                                      ]
                                                                                                                      [
                                                                                                                        {
                                                                                                                          [
                                                                                                                            PendingTxIn_match
                                                                                                                            ww
                                                                                                                          ]
                                                                                                                          [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                        }
                                                                                                                        (lam
                                                                                                                          ww
                                                                                                                          PendingTxOutRef
                                                                                                                          (lam
                                                                                                                            ww
                                                                                                                            [Maybe [[Tuple2 (con bytestring)] (con bytestring)]]
                                                                                                                            (lam
                                                                                                                              ww
                                                                                                                              [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
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
                                                                                                                                    plus
                                                                                                                                  ]
                                                                                                                                  {
                                                                                                                                    Nil
                                                                                                                                    [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                                  }
                                                                                                                                ]
                                                                                                                                [
                                                                                                                                  [
                                                                                                                                    {
                                                                                                                                      {
                                                                                                                                        map
                                                                                                                                        PendingTxOut
                                                                                                                                      }
                                                                                                                                      [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                                    }
                                                                                                                                    pendingTxOutValue
                                                                                                                                  ]
                                                                                                                                  [
                                                                                                                                    [
                                                                                                                                      wgetContinuingOutputs
                                                                                                                                      ww
                                                                                                                                    ]
                                                                                                                                    ww
                                                                                                                                  ]
                                                                                                                                ]
                                                                                                                              ]
                                                                                                                            )
                                                                                                                          )
                                                                                                                        )
                                                                                                                      ]
                                                                                                                    ]
                                                                                                                  ]
                                                                                                                )
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
                                                                                                                                lessThanEqInteger
                                                                                                                              ]
                                                                                                                              newAmount
                                                                                                                            ]
                                                                                                                            [
                                                                                                                              [
                                                                                                                                [
                                                                                                                                  unionWith
                                                                                                                                  addInteger
                                                                                                                                ]
                                                                                                                                [
                                                                                                                                  [
                                                                                                                                    availableFrom
                                                                                                                                    ww
                                                                                                                                  ]
                                                                                                                                  ww
                                                                                                                                ]
                                                                                                                              ]
                                                                                                                              [
                                                                                                                                [
                                                                                                                                  availableFrom
                                                                                                                                  ww
                                                                                                                                ]
                                                                                                                                ww
                                                                                                                              ]
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
                                                                                                                            [
                                                                                                                              checkBinRel
                                                                                                                              equalsInteger
                                                                                                                            ]
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
                                                                                                                                  plus
                                                                                                                                ]
                                                                                                                                {
                                                                                                                                  Nil
                                                                                                                                  [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                                }
                                                                                                                              ]
                                                                                                                              [
                                                                                                                                [
                                                                                                                                  {
                                                                                                                                    {
                                                                                                                                      map
                                                                                                                                      [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                                                                                                    }
                                                                                                                                    [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                                  }
                                                                                                                                  {
                                                                                                                                    {
                                                                                                                                      snd
                                                                                                                                      (con bytestring)
                                                                                                                                    }
                                                                                                                                    [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                                  }
                                                                                                                                ]
                                                                                                                                [
                                                                                                                                  [
                                                                                                                                    wscriptOutputsAt
                                                                                                                                    [
                                                                                                                                      {
                                                                                                                                        [
                                                                                                                                          PendingTxIn_match
                                                                                                                                          ww
                                                                                                                                        ]
                                                                                                                                        (con bytestring)
                                                                                                                                      }
                                                                                                                                      (lam
                                                                                                                                        ds
                                                                                                                                        PendingTxOutRef
                                                                                                                                        (lam
                                                                                                                                          ds
                                                                                                                                          [Maybe [[Tuple2 (con bytestring)] (con bytestring)]]
                                                                                                                                          (lam
                                                                                                                                            ds
                                                                                                                                            [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                                            [
                                                                                                                                              [
                                                                                                                                                [
                                                                                                                                                  {
                                                                                                                                                    [
                                                                                                                                                      {
                                                                                                                                                        Maybe_match
                                                                                                                                                        [[Tuple2 (con bytestring)] (con bytestring)]
                                                                                                                                                      }
                                                                                                                                                      ds
                                                                                                                                                    ]
                                                                                                                                                    (fun Unit (con bytestring))
                                                                                                                                                  }
                                                                                                                                                  (lam
                                                                                                                                                    h
                                                                                                                                                    [[Tuple2 (con bytestring)] (con bytestring)]
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
                                                                                                                                                              (con bytestring)
                                                                                                                                                            }
                                                                                                                                                            h
                                                                                                                                                          ]
                                                                                                                                                          (con bytestring)
                                                                                                                                                        }
                                                                                                                                                        (lam
                                                                                                                                                          a
                                                                                                                                                          (con bytestring)
                                                                                                                                                          (lam
                                                                                                                                                            ds
                                                                                                                                                            (con bytestring)
                                                                                                                                                            a
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
                                                                                                                                                    {
                                                                                                                                                      [
                                                                                                                                                        {
                                                                                                                                                          {
                                                                                                                                                            Tuple2_match
                                                                                                                                                            (con bytestring)
                                                                                                                                                          }
                                                                                                                                                          (con bytestring)
                                                                                                                                                        }
                                                                                                                                                        [
                                                                                                                                                          {
                                                                                                                                                            error
                                                                                                                                                            [[Tuple2 (con bytestring)] (con bytestring)]
                                                                                                                                                          }
                                                                                                                                                          Unit
                                                                                                                                                        ]
                                                                                                                                                      ]
                                                                                                                                                      (con bytestring)
                                                                                                                                                    }
                                                                                                                                                    (lam
                                                                                                                                                      a
                                                                                                                                                      (con bytestring)
                                                                                                                                                      (lam
                                                                                                                                                        ds
                                                                                                                                                        (con bytestring)
                                                                                                                                                        a
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
                                                                                                                                    ]
                                                                                                                                  ]
                                                                                                                                  ww
                                                                                                                                ]
                                                                                                                              ]
                                                                                                                            ]
                                                                                                                          ]
                                                                                                                          [
                                                                                                                            [
                                                                                                                              [
                                                                                                                                unionWith
                                                                                                                                subtractInteger
                                                                                                                              ]
                                                                                                                              [
                                                                                                                                [
                                                                                                                                  [
                                                                                                                                    unionWith
                                                                                                                                    addInteger
                                                                                                                                  ]
                                                                                                                                  [
                                                                                                                                    {
                                                                                                                                      [
                                                                                                                                        VestingTranche_match
                                                                                                                                        ww
                                                                                                                                      ]
                                                                                                                                      [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                                    }
                                                                                                                                    (lam
                                                                                                                                      ds
                                                                                                                                      (con integer)
                                                                                                                                      (lam
                                                                                                                                        ds
                                                                                                                                        [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                                        ds
                                                                                                                                      )
                                                                                                                                    )
                                                                                                                                  ]
                                                                                                                                ]
                                                                                                                                [
                                                                                                                                  {
                                                                                                                                    [
                                                                                                                                      VestingTranche_match
                                                                                                                                      ww
                                                                                                                                    ]
                                                                                                                                    [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                                  }
                                                                                                                                  (lam
                                                                                                                                    ds
                                                                                                                                    (con integer)
                                                                                                                                    (lam
                                                                                                                                      ds
                                                                                                                                      [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                                      ds
                                                                                                                                    )
                                                                                                                                  )
                                                                                                                                ]
                                                                                                                              ]
                                                                                                                            ]
                                                                                                                            newAmount
                                                                                                                          ]
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
                                                                                                          )
                                                                                                        )
                                                                                                      )
                                                                                                    )
                                                                                                  )
                                                                                                )
                                                                                              )
                                                                                              (let
                                                                                                (nonrec
                                                                                                )
                                                                                                (datatypebind
                                                                                                  (datatype
                                                                                                    (tyvardecl
                                                                                                      PendingTx
                                                                                                      (type)
                                                                                                    )
                                                                                                    
                                                                                                    PendingTx_match
                                                                                                    (vardecl
                                                                                                      PendingTx
                                                                                                      (fun [List PendingTxIn] (fun [List PendingTxOut] (fun (con integer) (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun PendingTxIn (fun [Interval (con integer)] (fun [List [[Tuple2 (con bytestring)] (con bytestring)]] (fun (con bytestring) PendingTx))))))))
                                                                                                    )
                                                                                                  )
                                                                                                )
                                                                                                (let
                                                                                                  (nonrec
                                                                                                  )
                                                                                                  (datatypebind
                                                                                                    (datatype
                                                                                                      (tyvardecl
                                                                                                        Vesting
                                                                                                        (type)
                                                                                                      )
                                                                                                      
                                                                                                      Vesting_match
                                                                                                      (vardecl
                                                                                                        Vesting
                                                                                                        (fun VestingTranche (fun VestingTranche (fun (con bytestring) Vesting)))
                                                                                                      )
                                                                                                    )
                                                                                                  )
                                                                                                  (let
                                                                                                    (nonrec
                                                                                                    )
                                                                                                    (datatypebind
                                                                                                      (datatype
                                                                                                        (tyvardecl
                                                                                                          VestingData
                                                                                                          (type)
                                                                                                        )
                                                                                                        
                                                                                                        VestingData_match
                                                                                                        (vardecl
                                                                                                          VestingData
                                                                                                          (fun (con bytestring) (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] VestingData))
                                                                                                        )
                                                                                                      )
                                                                                                    )
                                                                                                    (let
                                                                                                      (nonrec
                                                                                                      )
                                                                                                      (termbind
                                                                                                        (strict
                                                                                                        )
                                                                                                        (vardecl
                                                                                                          mkValidator
                                                                                                          (fun Vesting (fun VestingData (fun Unit (fun PendingTx Bool))))
                                                                                                        )
                                                                                                        (lam
                                                                                                          w
                                                                                                          Vesting
                                                                                                          (lam
                                                                                                            w
                                                                                                            VestingData
                                                                                                            (lam
                                                                                                              w
                                                                                                              Unit
                                                                                                              (lam
                                                                                                                w
                                                                                                                PendingTx
                                                                                                                [
                                                                                                                  {
                                                                                                                    [
                                                                                                                      Vesting_match
                                                                                                                      w
                                                                                                                    ]
                                                                                                                    Bool
                                                                                                                  }
                                                                                                                  (lam
                                                                                                                    ww
                                                                                                                    VestingTranche
                                                                                                                    (lam
                                                                                                                      ww
                                                                                                                      VestingTranche
                                                                                                                      (lam
                                                                                                                        ww
                                                                                                                        (con bytestring)
                                                                                                                        [
                                                                                                                          {
                                                                                                                            [
                                                                                                                              VestingData_match
                                                                                                                              w
                                                                                                                            ]
                                                                                                                            Bool
                                                                                                                          }
                                                                                                                          (lam
                                                                                                                            ww
                                                                                                                            (con bytestring)
                                                                                                                            (lam
                                                                                                                              ww
                                                                                                                              [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                              [
                                                                                                                                [
                                                                                                                                  {
                                                                                                                                    [
                                                                                                                                      Unit_match
                                                                                                                                      w
                                                                                                                                    ]
                                                                                                                                    (fun Unit Bool)
                                                                                                                                  }
                                                                                                                                  (lam
                                                                                                                                    thunk
                                                                                                                                    Unit
                                                                                                                                    [
                                                                                                                                      {
                                                                                                                                        [
                                                                                                                                          PendingTx_match
                                                                                                                                          w
                                                                                                                                        ]
                                                                                                                                        Bool
                                                                                                                                      }
                                                                                                                                      (lam
                                                                                                                                        ww
                                                                                                                                        [List PendingTxIn]
                                                                                                                                        (lam
                                                                                                                                          ww
                                                                                                                                          [List PendingTxOut]
                                                                                                                                          (lam
                                                                                                                                            ww
                                                                                                                                            (con integer)
                                                                                                                                            (lam
                                                                                                                                              ww
                                                                                                                                              [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                                              (lam
                                                                                                                                                ww
                                                                                                                                                PendingTxIn
                                                                                                                                                (lam
                                                                                                                                                  ww
                                                                                                                                                  [Interval (con integer)]
                                                                                                                                                  (lam
                                                                                                                                                    ww
                                                                                                                                                    [List [[Tuple2 (con bytestring)] (con bytestring)]]
                                                                                                                                                    (lam
                                                                                                                                                      ww
                                                                                                                                                      (con bytestring)
                                                                                                                                                      [
                                                                                                                                                        [
                                                                                                                                                          [
                                                                                                                                                            [
                                                                                                                                                              [
                                                                                                                                                                [
                                                                                                                                                                  [
                                                                                                                                                                    wmkValidator
                                                                                                                                                                    ww
                                                                                                                                                                  ]
                                                                                                                                                                  ww
                                                                                                                                                                ]
                                                                                                                                                                ww
                                                                                                                                                              ]
                                                                                                                                                              Unit
                                                                                                                                                            ]
                                                                                                                                                            ww
                                                                                                                                                          ]
                                                                                                                                                          ww
                                                                                                                                                        ]
                                                                                                                                                        ww
                                                                                                                                                      ]
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
                                                                                                                                Unit
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
    )
  )
)