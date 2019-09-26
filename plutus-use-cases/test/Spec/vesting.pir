(program
  (let
    (nonrec)
    (datatypebind
      (datatype (tyvardecl Unit (type))  Unit_match (vardecl Unit Unit))
    )
    (let
      (nonrec)
      (termbind (strict) (vardecl fAdditiveGroupValue (con integer)) (con -1))
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
              (vardecl Nil [List a])
              (vardecl Cons (fun a (fun [List a] [List a])))
            )
          )
          (let
            (nonrec)
            (termbind
              (strict)
              (vardecl
                multiplyInteger
                (fun (con integer) (fun (con integer) (con integer)))
              )
              (builtin multiplyInteger)
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
                                                                                multiplyInteger
                                                                                i
                                                                              ]
                                                                              i
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
                                                        Unit
                                                      ]
                                                    )
                                                  )
                                                  [ go i ]
                                                )
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
                      [ go ds ]
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
                    (rec)
                    (datatypebind
                      (datatype
                        (tyvardecl Data (type))
                        
                        Data_match
                        (vardecl B (fun (con bytestring) Data))
                        (vardecl
                          Constr (fun (con integer) (fun [List Data] Data))
                        )
                        (vardecl I (fun (con integer) Data))
                        (vardecl Map (fun [List [[Tuple2 Data] Data]] Data))
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
                            (tyvardecl IsData (fun (type) (type)))
                            (tyvardecl a (type))
                            IsData_match
                            (vardecl
                              CConsIsData
                              (fun (fun a Data) (fun (fun Data [Maybe a]) [IsData a]))
                            )
                          )
                        )
                        (let
                          (nonrec)
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
                                    {
                                      [ { IsData_match a } v ]
                                      (fun Data [Maybe a])
                                    }
                                    (lam
                                      v
                                      (fun a Data)
                                      (lam v (fun Data [Maybe a]) v)
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
                                                        {
                                                          Nothing [[Tuple2 a] b]
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
                                                              ad
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
                                                                        bd
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
                                                                                                        ad
                                                                                                      ]
                                                                                                    ]
                                                                                                    (fun Unit [Maybe [[Tuple2 a] b]])
                                                                                                  }
                                                                                                  (lam
                                                                                                    a
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
                                                                                                                  bd
                                                                                                                ]
                                                                                                              ]
                                                                                                              (fun Unit [Maybe [[Tuple2 a] b]])
                                                                                                            }
                                                                                                            (lam
                                                                                                              x
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
                                                                                                                      a
                                                                                                                    ]
                                                                                                                    x
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
                                                [List [[Tuple2 Data] Data]]
                                                (lam
                                                  thunk
                                                  Unit
                                                  { Nothing [[Tuple2 a] b] }
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
                                    build
                                    (all a (type) (fun (all b (type) (fun (fun a (fun b b)) (fun b b))) [List a]))
                                  )
                                  (abs
                                    a
                                    (type)
                                    (lam
                                      g
                                      (all b (type) (fun (fun a (fun b b)) (fun b b)))
                                      [
                                        [ { g [List a] } { Cons a } ] { Nil a }
                                      ]
                                    )
                                  )
                                )
                                (let
                                  (nonrec)
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
                                          {
                                            [ { IsData_match a } v ]
                                            (fun a Data)
                                          }
                                          (lam
                                            v
                                            (fun a Data)
                                            (lam v (fun Data [Maybe a]) v)
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
                                                  {
                                                    [
                                                      { { Tuple2_match a } b }
                                                      ds
                                                    ]
                                                    Data
                                                  }
                                                  (lam
                                                    a
                                                    a
                                                    (lam
                                                      b
                                                      b
                                                      [
                                                        [ Constr (con 0) ]
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
                                                                        {
                                                                          toData
                                                                          a
                                                                        }
                                                                        dIsData
                                                                      ]
                                                                      a
                                                                    ]
                                                                  ]
                                                                  [
                                                                    [
                                                                      c
                                                                      [
                                                                        [
                                                                          {
                                                                            toData
                                                                            b
                                                                          }
                                                                          dIsData
                                                                        ]
                                                                        b
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
                                    (let
                                      (nonrec)
                                      (termbind
                                        (strict)
                                        (vardecl
                                          fIsDataTuple2
                                          (all a (type) (all b (type) (fun [IsData a] (fun [IsData b] [IsData [[Tuple2 a] b]]))))
                                        )
                                        (abs
                                          a
                                          (type)
                                          (abs
                                            b
                                            (type)
                                            (lam
                                              v
                                              [IsData a]
                                              (lam
                                                v
                                                [IsData b]
                                                [
                                                  [
                                                    {
                                                      CConsIsData [[Tuple2 a] b]
                                                    }
                                                    [
                                                      [
                                                        {
                                                          {
                                                            fIsDataTuple2_ctoData
                                                            a
                                                          }
                                                          b
                                                        }
                                                        v
                                                      ]
                                                      v
                                                    ]
                                                  ]
                                                  [
                                                    [
                                                      {
                                                        {
                                                          fIsDataTuple2_cfromData
                                                          a
                                                        }
                                                        b
                                                      }
                                                      v
                                                    ]
                                                    v
                                                  ]
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
                                                          [
                                                            {
                                                              Just
                                                              (con bytestring)
                                                            }
                                                            b
                                                          ]
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
                                                            (con bytestring)
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
                                                        Nothing (con bytestring)
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
                                                    { Nothing (con bytestring) }
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
                                              fIsDataCurrencySymbol
                                              [IsData (con bytestring)]
                                            )
                                            [
                                              [
                                                { CConsIsData (con bytestring) }
                                                B
                                              ]
                                              fIsDataByteString_cfromData
                                            ]
                                          )
                                          (let
                                            (nonrec)
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
                                                          {
                                                            [ Data_match ds ]
                                                            (fun Unit [Maybe (con integer)])
                                                          }
                                                          (lam
                                                            default_arg0
                                                            (con bytestring)
                                                            (lam
                                                              thunk
                                                              Unit
                                                              {
                                                                Nothing
                                                                (con integer)
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
                                                                (con integer)
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
                                                              Just (con integer)
                                                            }
                                                            i
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
                                                          Nothing (con integer)
                                                        }
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
                                                  fIsDataInteger
                                                  [IsData (con integer)]
                                                )
                                                [
                                                  [
                                                    {
                                                      CConsIsData (con integer)
                                                    }
                                                    I
                                                  ]
                                                  fIsDataInteger_cfromData
                                                ]
                                              )
                                              (let
                                                (rec)
                                                (termbind
                                                  (strict)
                                                  (vardecl
                                                    fIsDataNil_cfromData
                                                    (all a (type) (fun [IsData a] (fun Data [Maybe [List a]])))
                                                  )
                                                  (abs
                                                    a
                                                    (type)
                                                    (lam
                                                      dIsData
                                                      [IsData a]
                                                      (lam
                                                        ds
                                                        Data
                                                        [
                                                          [
                                                            [
                                                              [
                                                                [
                                                                  {
                                                                    [
                                                                      Data_match
                                                                      ds
                                                                    ]
                                                                    (fun Unit [Maybe [List a]])
                                                                  }
                                                                  (lam
                                                                    default_arg0
                                                                    (con bytestring)
                                                                    (lam
                                                                      thunk
                                                                      Unit
                                                                      {
                                                                        Nothing
                                                                        [List a]
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
                                                                              [
                                                                                {
                                                                                  Nil_match
                                                                                  Data
                                                                                }
                                                                                ds
                                                                              ]
                                                                              (fun Unit [Maybe [List a]])
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
                                                                                            0
                                                                                          )
                                                                                        ]
                                                                                      ]
                                                                                      (fun Unit [Maybe [List a]])
                                                                                    }
                                                                                    (lam
                                                                                      thunk
                                                                                      Unit
                                                                                      [
                                                                                        {
                                                                                          Just
                                                                                          [List a]
                                                                                        }
                                                                                        {
                                                                                          Nil
                                                                                          a
                                                                                        }
                                                                                      ]
                                                                                    )
                                                                                  ]
                                                                                  (lam
                                                                                    thunk
                                                                                    Unit
                                                                                    {
                                                                                      Nothing
                                                                                      [List a]
                                                                                    }
                                                                                  )
                                                                                ]
                                                                                Unit
                                                                              ]
                                                                            )
                                                                          ]
                                                                          (lam
                                                                            hd
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
                                                                                        (fun Unit [Maybe [List a]])
                                                                                      }
                                                                                      (lam
                                                                                        thunk
                                                                                        Unit
                                                                                        {
                                                                                          Nothing
                                                                                          [List a]
                                                                                        }
                                                                                      )
                                                                                    ]
                                                                                    (lam
                                                                                      td
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
                                                                                                  (fun Unit [Maybe [List a]])
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
                                                                                                                1
                                                                                                              )
                                                                                                            ]
                                                                                                          ]
                                                                                                          (fun Unit [Maybe [List a]])
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
                                                                                                                      hd
                                                                                                                    ]
                                                                                                                  ]
                                                                                                                  (fun Unit [Maybe [List a]])
                                                                                                                }
                                                                                                                (lam
                                                                                                                  a
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
                                                                                                                                [List a]
                                                                                                                              }
                                                                                                                              [
                                                                                                                                [
                                                                                                                                  {
                                                                                                                                    fIsDataNil_cfromData
                                                                                                                                    a
                                                                                                                                  }
                                                                                                                                  dIsData
                                                                                                                                ]
                                                                                                                                td
                                                                                                                              ]
                                                                                                                            ]
                                                                                                                            (fun Unit [Maybe [List a]])
                                                                                                                          }
                                                                                                                          (lam
                                                                                                                            x
                                                                                                                            [List a]
                                                                                                                            (lam
                                                                                                                              thunk
                                                                                                                              Unit
                                                                                                                              [
                                                                                                                                {
                                                                                                                                  Just
                                                                                                                                  [List a]
                                                                                                                                }
                                                                                                                                [
                                                                                                                                  [
                                                                                                                                    {
                                                                                                                                      Cons
                                                                                                                                      a
                                                                                                                                    }
                                                                                                                                    a
                                                                                                                                  ]
                                                                                                                                  x
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
                                                                                                                            [List a]
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
                                                                                                                  [List a]
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
                                                                                                          [List a]
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
                                                                                                      [List a]
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
                                                                    [List a]
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
                                                                  [List a]
                                                                }
                                                              )
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
                                                            [
                                                              {
                                                                fIsDataNil_cfromData
                                                                [[Tuple2 k] v]
                                                              }
                                                              [
                                                                [
                                                                  {
                                                                    {
                                                                      fIsDataTuple2
                                                                      k
                                                                    }
                                                                    v
                                                                  }
                                                                  dIsData
                                                                ]
                                                                dIsData
                                                              ]
                                                            ]
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
                                                        fIsDataNil_ctoData
                                                        (all a (type) (fun [IsData a] (fun [List a] Data)))
                                                      )
                                                      (abs
                                                        a
                                                        (type)
                                                        (lam
                                                          dIsData
                                                          [IsData a]
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
                                                                    (fun Unit Data)
                                                                  }
                                                                  (lam
                                                                    thunk
                                                                    Unit
                                                                    [
                                                                      [
                                                                        Constr
                                                                        (con 0)
                                                                      ]
                                                                      {
                                                                        Nil Data
                                                                      }
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
                                                                          Constr
                                                                          (con 1
                                                                          )
                                                                        ]
                                                                        [
                                                                          {
                                                                            build
                                                                            Data
                                                                          }
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
                                                                                        {
                                                                                          toData
                                                                                          a
                                                                                        }
                                                                                        dIsData
                                                                                      ]
                                                                                      x
                                                                                    ]
                                                                                  ]
                                                                                  [
                                                                                    [
                                                                                      c
                                                                                      [
                                                                                        [
                                                                                          {
                                                                                            fIsDataNil_ctoData
                                                                                            a
                                                                                          }
                                                                                          dIsData
                                                                                        ]
                                                                                        xs
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
                                                                [
                                                                  {
                                                                    fIsDataNil_ctoData
                                                                    [[Tuple2 k] v]
                                                                  }
                                                                  [
                                                                    [
                                                                      {
                                                                        {
                                                                          fIsDataTuple2
                                                                          k
                                                                        }
                                                                        v
                                                                      }
                                                                      dIsData
                                                                    ]
                                                                    dIsData
                                                                  ]
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
                                                                      [
                                                                        [
                                                                          {
                                                                            {
                                                                              fIsDataMap
                                                                              k
                                                                            }
                                                                            v
                                                                          }
                                                                          v
                                                                        ]
                                                                        v
                                                                      ]
                                                                    ]
                                                                    [
                                                                      [
                                                                        {
                                                                          {
                                                                            fIsDataMap
                                                                            k
                                                                          }
                                                                          v
                                                                        }
                                                                        v
                                                                      ]
                                                                      v
                                                                    ]
                                                                  ]
                                                                )
                                                              )
                                                            )
                                                          )
                                                        )
                                                        (let
                                                          (nonrec)
                                                          (termbind
                                                            (nonstrict)
                                                            (vardecl
                                                              fIsDataTokenName
                                                              [IsData (con bytestring)]
                                                            )
                                                            [
                                                              [
                                                                {
                                                                  CConsIsData
                                                                  (con bytestring)
                                                                }
                                                                B
                                                              ]
                                                              fIsDataByteString_cfromData
                                                            ]
                                                          )
                                                          (let
                                                            (nonrec)
                                                            (termbind
                                                              (nonstrict)
                                                              (vardecl
                                                                fIsDataValue
                                                                [IsData [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                              )
                                                              [
                                                                [
                                                                  {
                                                                    {
                                                                      fIsDataMap
                                                                      (con bytestring)
                                                                    }
                                                                    (con integer)
                                                                  }
                                                                  fIsDataTokenName
                                                                ]
                                                                fIsDataInteger
                                                              ]
                                                            )
                                                            (let
                                                              (nonrec)
                                                              (termbind
                                                                (nonstrict)
                                                                (vardecl
                                                                  fIsDataValue
                                                                  [IsData [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                                )
                                                                [
                                                                  [
                                                                    {
                                                                      {
                                                                        fIsDataTuple2
                                                                        (con bytestring)
                                                                      }
                                                                      [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]
                                                                    }
                                                                    fIsDataCurrencySymbol
                                                                  ]
                                                                  fIsDataValue
                                                                ]
                                                              )
                                                              (let
                                                                (nonrec)
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
                                                                  (nonrec)
                                                                  (termbind
                                                                    (strict)
                                                                    (vardecl
                                                                      fIsDataVestingData_cfromData
                                                                      (fun Data [Maybe VestingData])
                                                                    )
                                                                    (lam
                                                                      ds
                                                                      Data
                                                                      [
                                                                        [
                                                                          [
                                                                            [
                                                                              [
                                                                                {
                                                                                  [
                                                                                    Data_match
                                                                                    ds
                                                                                  ]
                                                                                  (fun Unit [Maybe VestingData])
                                                                                }
                                                                                (lam
                                                                                  default_arg0
                                                                                  (con bytestring)
                                                                                  (lam
                                                                                    thunk
                                                                                    Unit
                                                                                    {
                                                                                      Nothing
                                                                                      VestingData
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
                                                                                            [
                                                                                              {
                                                                                                Nil_match
                                                                                                Data
                                                                                              }
                                                                                              ds
                                                                                            ]
                                                                                            (fun Unit [Maybe VestingData])
                                                                                          }
                                                                                          (lam
                                                                                            thunk
                                                                                            Unit
                                                                                            {
                                                                                              Nothing
                                                                                              VestingData
                                                                                            }
                                                                                          )
                                                                                        ]
                                                                                        (lam
                                                                                          h
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
                                                                                                      (fun Unit [Maybe VestingData])
                                                                                                    }
                                                                                                    (lam
                                                                                                      thunk
                                                                                                      Unit
                                                                                                      {
                                                                                                        Nothing
                                                                                                        VestingData
                                                                                                      }
                                                                                                    )
                                                                                                  ]
                                                                                                  (lam
                                                                                                    v
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
                                                                                                                (fun Unit [Maybe VestingData])
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
                                                                                                                              0
                                                                                                                            )
                                                                                                                          ]
                                                                                                                        ]
                                                                                                                        (fun Unit [Maybe VestingData])
                                                                                                                      }
                                                                                                                      (lam
                                                                                                                        thunk
                                                                                                                        Unit
                                                                                                                        [
                                                                                                                          [
                                                                                                                            [
                                                                                                                              [
                                                                                                                                [
                                                                                                                                  {
                                                                                                                                    [
                                                                                                                                      Data_match
                                                                                                                                      h
                                                                                                                                    ]
                                                                                                                                    (fun Unit [Maybe VestingData])
                                                                                                                                  }
                                                                                                                                  (lam
                                                                                                                                    b
                                                                                                                                    (con bytestring)
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
                                                                                                                                                    {
                                                                                                                                                      fIsDataNil_cfromData
                                                                                                                                                      [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                                                    }
                                                                                                                                                    fIsDataValue
                                                                                                                                                  ]
                                                                                                                                                  v
                                                                                                                                                ]
                                                                                                                                              ]
                                                                                                                                              (fun Unit [Maybe VestingData])
                                                                                                                                            }
                                                                                                                                            (lam
                                                                                                                                              x
                                                                                                                                              [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                                              (lam
                                                                                                                                                thunk
                                                                                                                                                Unit
                                                                                                                                                [
                                                                                                                                                  {
                                                                                                                                                    Just
                                                                                                                                                    VestingData
                                                                                                                                                  }
                                                                                                                                                  [
                                                                                                                                                    [
                                                                                                                                                      VestingData
                                                                                                                                                      b
                                                                                                                                                    ]
                                                                                                                                                    x
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
                                                                                                                                              VestingData
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
                                                                                                                                  (con integer)
                                                                                                                                  (lam
                                                                                                                                    default_arg1
                                                                                                                                    [List Data]
                                                                                                                                    (lam
                                                                                                                                      thunk
                                                                                                                                      Unit
                                                                                                                                      {
                                                                                                                                        Nothing
                                                                                                                                        VestingData
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
                                                                                                                                    VestingData
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
                                                                                                                                  VestingData
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
                                                                                                                        VestingData
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
                                                                                                                    VestingData
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
                                                                                  VestingData
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
                                                                                VestingData
                                                                              }
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
                                                                                    [
                                                                                      {
                                                                                        b
                                                                                        Bool
                                                                                      }
                                                                                      True
                                                                                    ]
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
                                                                                                    f
                                                                                                    x
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
                                                                            (nonrec
                                                                            )
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
                                                                                      fMonoidValue_c
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
                                                                                    (datatypebind
                                                                                      (datatype
                                                                                        (tyvardecl
                                                                                          Extended
                                                                                          (fun (type) (type))
                                                                                        )
                                                                                        (tyvardecl
                                                                                          a
                                                                                          (type)
                                                                                        )
                                                                                        Extended_match
                                                                                        (vardecl
                                                                                          Finite
                                                                                          (fun a [Extended a])
                                                                                        )
                                                                                        (vardecl
                                                                                          NegInf
                                                                                          [Extended a]
                                                                                        )
                                                                                        (vardecl
                                                                                          PosInf
                                                                                          [Extended a]
                                                                                        )
                                                                                      )
                                                                                    )
                                                                                    (let
                                                                                      (nonrec
                                                                                      )
                                                                                      (datatypebind
                                                                                        (datatype
                                                                                          (tyvardecl
                                                                                            UpperBound
                                                                                            (fun (type) (type))
                                                                                          )
                                                                                          (tyvardecl
                                                                                            a
                                                                                            (type)
                                                                                          )
                                                                                          UpperBound_match
                                                                                          (vardecl
                                                                                            UpperBound
                                                                                            (fun [Extended a] (fun Bool [UpperBound a]))
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
                                                                                                  [
                                                                                                    [
                                                                                                      {
                                                                                                        b
                                                                                                        Bool
                                                                                                      }
                                                                                                      True
                                                                                                    ]
                                                                                                    False
                                                                                                  ]
                                                                                                )
                                                                                                [
                                                                                                  [
                                                                                                    (builtin
                                                                                                      lessThanEqualsInteger
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
                                                                                          (nonrec
                                                                                          )
                                                                                          (termbind
                                                                                            (strict
                                                                                            )
                                                                                            (vardecl
                                                                                              wavailableFrom
                                                                                              (fun (con integer) (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun [Extended (con integer)] (fun Bool (fun [UpperBound (con integer)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]])))))
                                                                                            )
                                                                                            (lam
                                                                                              ww
                                                                                              (con integer)
                                                                                              (lam
                                                                                                ww
                                                                                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                (lam
                                                                                                  ww
                                                                                                  [Extended (con integer)]
                                                                                                  (lam
                                                                                                    ww
                                                                                                    Bool
                                                                                                    (lam
                                                                                                      ww
                                                                                                      [UpperBound (con integer)]
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
                                                                                                                (fun Unit [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]])
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
                                                                                                                                ww
                                                                                                                              ]
                                                                                                                              ipv
                                                                                                                            ]
                                                                                                                          ]
                                                                                                                          (fun Unit [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]])
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
                                                                                                                                  (fun Unit [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]])
                                                                                                                                }
                                                                                                                                (lam
                                                                                                                                  thunk
                                                                                                                                  Unit
                                                                                                                                  [
                                                                                                                                    {
                                                                                                                                      [
                                                                                                                                        {
                                                                                                                                          UpperBound_match
                                                                                                                                          (con integer)
                                                                                                                                        }
                                                                                                                                        ww
                                                                                                                                      ]
                                                                                                                                      [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
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
                                                                                                                                                {
                                                                                                                                                  [
                                                                                                                                                    {
                                                                                                                                                      Extended_match
                                                                                                                                                      (con integer)
                                                                                                                                                    }
                                                                                                                                                    ww
                                                                                                                                                  ]
                                                                                                                                                  (fun Unit [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]])
                                                                                                                                                }
                                                                                                                                                (lam
                                                                                                                                                  default_arg0
                                                                                                                                                  (con integer)
                                                                                                                                                  (lam
                                                                                                                                                    thunk
                                                                                                                                                    Unit
                                                                                                                                                    ww
                                                                                                                                                  )
                                                                                                                                                )
                                                                                                                                              ]
                                                                                                                                              (lam
                                                                                                                                                thunk
                                                                                                                                                Unit
                                                                                                                                                ww
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
                                                                                                                                                      (fun Unit [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]])
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
                                                                                                                                                    ww
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
                                                                                                                                )
                                                                                                                              ]
                                                                                                                              (lam
                                                                                                                                thunk
                                                                                                                                Unit
                                                                                                                                [
                                                                                                                                  {
                                                                                                                                    [
                                                                                                                                      {
                                                                                                                                        UpperBound_match
                                                                                                                                        (con integer)
                                                                                                                                      }
                                                                                                                                      ww
                                                                                                                                    ]
                                                                                                                                    [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
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
                                                                                                                                              {
                                                                                                                                                [
                                                                                                                                                  {
                                                                                                                                                    Extended_match
                                                                                                                                                    (con integer)
                                                                                                                                                  }
                                                                                                                                                  ww
                                                                                                                                                ]
                                                                                                                                                (fun Unit [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]])
                                                                                                                                              }
                                                                                                                                              (lam
                                                                                                                                                default_arg0
                                                                                                                                                (con integer)
                                                                                                                                                (lam
                                                                                                                                                  thunk
                                                                                                                                                  Unit
                                                                                                                                                  ww
                                                                                                                                                )
                                                                                                                                              )
                                                                                                                                            ]
                                                                                                                                            (lam
                                                                                                                                              thunk
                                                                                                                                              Unit
                                                                                                                                              ww
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
                                                                                                                                                    (fun Unit [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]])
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
                                                                                                                                                  ww
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
                                                                                                                              {
                                                                                                                                [
                                                                                                                                  Bool_match
                                                                                                                                  [
                                                                                                                                    [
                                                                                                                                      lessThanEqInteger
                                                                                                                                      ww
                                                                                                                                    ]
                                                                                                                                    ipv
                                                                                                                                  ]
                                                                                                                                ]
                                                                                                                                (fun Unit [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]])
                                                                                                                              }
                                                                                                                              (lam
                                                                                                                                thunk
                                                                                                                                Unit
                                                                                                                                [
                                                                                                                                  {
                                                                                                                                    [
                                                                                                                                      {
                                                                                                                                        UpperBound_match
                                                                                                                                        (con integer)
                                                                                                                                      }
                                                                                                                                      ww
                                                                                                                                    ]
                                                                                                                                    [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
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
                                                                                                                                              {
                                                                                                                                                [
                                                                                                                                                  {
                                                                                                                                                    Extended_match
                                                                                                                                                    (con integer)
                                                                                                                                                  }
                                                                                                                                                  ww
                                                                                                                                                ]
                                                                                                                                                (fun Unit [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]])
                                                                                                                                              }
                                                                                                                                              (lam
                                                                                                                                                default_arg0
                                                                                                                                                (con integer)
                                                                                                                                                (lam
                                                                                                                                                  thunk
                                                                                                                                                  Unit
                                                                                                                                                  ww
                                                                                                                                                )
                                                                                                                                              )
                                                                                                                                            ]
                                                                                                                                            (lam
                                                                                                                                              thunk
                                                                                                                                              Unit
                                                                                                                                              ww
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
                                                                                                                                                    (fun Unit [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]])
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
                                                                                                                                                  ww
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
                                                                                                                Nil
                                                                                                                [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                              }
                                                                                                            )
                                                                                                          ]
                                                                                                          (lam
                                                                                                            thunk
                                                                                                            Unit
                                                                                                            [
                                                                                                              {
                                                                                                                [
                                                                                                                  {
                                                                                                                    UpperBound_match
                                                                                                                    (con integer)
                                                                                                                  }
                                                                                                                  ww
                                                                                                                ]
                                                                                                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
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
                                                                                                                          {
                                                                                                                            [
                                                                                                                              {
                                                                                                                                Extended_match
                                                                                                                                (con integer)
                                                                                                                              }
                                                                                                                              ww
                                                                                                                            ]
                                                                                                                            (fun Unit [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]])
                                                                                                                          }
                                                                                                                          (lam
                                                                                                                            default_arg0
                                                                                                                            (con integer)
                                                                                                                            (lam
                                                                                                                              thunk
                                                                                                                              Unit
                                                                                                                              ww
                                                                                                                            )
                                                                                                                          )
                                                                                                                        ]
                                                                                                                        (lam
                                                                                                                          thunk
                                                                                                                          Unit
                                                                                                                          ww
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
                                                                                                                                (fun Unit [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]])
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
                                                                                                                              ww
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
                                                                                            (nonrec
                                                                                            )
                                                                                            (datatypebind
                                                                                              (datatype
                                                                                                (tyvardecl
                                                                                                  PendingTxOutType
                                                                                                  (type)
                                                                                                )
                                                                                                
                                                                                                PendingTxOutType_match
                                                                                                (vardecl
                                                                                                  DataTxOut
                                                                                                  PendingTxOutType
                                                                                                )
                                                                                                (vardecl
                                                                                                  PubKeyTxOut
                                                                                                  (fun (con bytestring) PendingTxOutType)
                                                                                                )
                                                                                              )
                                                                                            )
                                                                                            (let
                                                                                              (nonrec
                                                                                              )
                                                                                              (datatypebind
                                                                                                (datatype
                                                                                                  (tyvardecl
                                                                                                    PendingTxOut
                                                                                                    (type)
                                                                                                  )
                                                                                                  
                                                                                                  PendingTxOut_match
                                                                                                  (vardecl
                                                                                                    PendingTxOut
                                                                                                    (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun [Maybe [[Tuple2 (con bytestring)] (con bytestring)]] (fun PendingTxOutType PendingTxOut)))
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
                                                                                                    wgetContinuingOutputs
                                                                                                    (fun [List PendingTxOut] (fun (con bytestring) [List PendingTxOut]))
                                                                                                  )
                                                                                                  (lam
                                                                                                    ww
                                                                                                    [List PendingTxOut]
                                                                                                    (lam
                                                                                                      ww
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
                                                                                                                                                      ww
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
                                                                                                )
                                                                                                (let
                                                                                                  (nonrec
                                                                                                  )
                                                                                                  (termbind
                                                                                                    (strict
                                                                                                    )
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
                                                                                                    (nonrec
                                                                                                    )
                                                                                                    (datatypebind
                                                                                                      (datatype
                                                                                                        (tyvardecl
                                                                                                          LowerBound
                                                                                                          (fun (type) (type))
                                                                                                        )
                                                                                                        (tyvardecl
                                                                                                          a
                                                                                                          (type)
                                                                                                        )
                                                                                                        LowerBound_match
                                                                                                        (vardecl
                                                                                                          LowerBound
                                                                                                          (fun [Extended a] (fun Bool [LowerBound a]))
                                                                                                        )
                                                                                                      )
                                                                                                    )
                                                                                                    (let
                                                                                                      (nonrec
                                                                                                      )
                                                                                                      (datatypebind
                                                                                                        (datatype
                                                                                                          (tyvardecl
                                                                                                            Interval
                                                                                                            (fun (type) (type))
                                                                                                          )
                                                                                                          (tyvardecl
                                                                                                            a
                                                                                                            (type)
                                                                                                          )
                                                                                                          Interval_match
                                                                                                          (vardecl
                                                                                                            Interval
                                                                                                            (fun [LowerBound a] (fun [UpperBound a] [Interval a]))
                                                                                                          )
                                                                                                        )
                                                                                                      )
                                                                                                      (let
                                                                                                        (nonrec
                                                                                                        )
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
                                                                                                          (nonrec
                                                                                                          )
                                                                                                          (datatypebind
                                                                                                            (datatype
                                                                                                              (tyvardecl
                                                                                                                PendingTxIn
                                                                                                                (fun (type) (type))
                                                                                                              )
                                                                                                              (tyvardecl
                                                                                                                w
                                                                                                                (type)
                                                                                                              )
                                                                                                              PendingTxIn_match
                                                                                                              (vardecl
                                                                                                                PendingTxIn
                                                                                                                (fun PendingTxOutRef (fun w (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] [PendingTxIn w])))
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
                                                                                                                  (fun (type) (type))
                                                                                                                )
                                                                                                                (tyvardecl
                                                                                                                  i
                                                                                                                  (type)
                                                                                                                )
                                                                                                                PendingTx_match
                                                                                                                (vardecl
                                                                                                                  PendingTx
                                                                                                                  (fun [List [PendingTxIn [Maybe [[Tuple2 (con bytestring)] (con bytestring)]]]] (fun [List PendingTxOut] (fun (con integer) (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun i (fun [Interval (con integer)] (fun [List [[Tuple2 (con bytestring)] (con bytestring)]] (fun (con bytestring) [PendingTx i]))))))))
                                                                                                                )
                                                                                                              )
                                                                                                            )
                                                                                                            (let
                                                                                                              (nonrec
                                                                                                              )
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
                                                                                                                (nonrec
                                                                                                                )
                                                                                                                (termbind
                                                                                                                  (strict
                                                                                                                  )
                                                                                                                  (vardecl
                                                                                                                    availableFrom
                                                                                                                    (fun VestingTranche (fun [Interval (con integer)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]))
                                                                                                                  )
                                                                                                                  (lam
                                                                                                                    w
                                                                                                                    VestingTranche
                                                                                                                    (lam
                                                                                                                      w
                                                                                                                      [Interval (con integer)]
                                                                                                                      [
                                                                                                                        {
                                                                                                                          [
                                                                                                                            VestingTranche_match
                                                                                                                            w
                                                                                                                          ]
                                                                                                                          [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                        }
                                                                                                                        (lam
                                                                                                                          ww
                                                                                                                          (con integer)
                                                                                                                          (lam
                                                                                                                            ww
                                                                                                                            [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                            [
                                                                                                                              {
                                                                                                                                [
                                                                                                                                  {
                                                                                                                                    Interval_match
                                                                                                                                    (con integer)
                                                                                                                                  }
                                                                                                                                  w
                                                                                                                                ]
                                                                                                                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
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
                                                                                                                                      [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
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
                                                                                                                                                  wavailableFrom
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
                                                                                                                                wmkValidator
                                                                                                                                (fun VestingTranche (fun VestingTranche (fun Data (fun [PendingTx [PendingTxIn [[Tuple2 (con bytestring)] (con bytestring)]]] Bool))))
                                                                                                                              )
                                                                                                                              (lam
                                                                                                                                ww
                                                                                                                                VestingTranche
                                                                                                                                (lam
                                                                                                                                  ww
                                                                                                                                  VestingTranche
                                                                                                                                  (lam
                                                                                                                                    w
                                                                                                                                    Data
                                                                                                                                    (lam
                                                                                                                                      w
                                                                                                                                      [PendingTx [PendingTxIn [[Tuple2 (con bytestring)] (con bytestring)]]]
                                                                                                                                      [
                                                                                                                                        [
                                                                                                                                          [
                                                                                                                                            {
                                                                                                                                              [
                                                                                                                                                {
                                                                                                                                                  Maybe_match
                                                                                                                                                  VestingData
                                                                                                                                                }
                                                                                                                                                [
                                                                                                                                                  fIsDataVestingData_cfromData
                                                                                                                                                  w
                                                                                                                                                ]
                                                                                                                                              ]
                                                                                                                                              (fun Unit Bool)
                                                                                                                                            }
                                                                                                                                            (lam
                                                                                                                                              ds
                                                                                                                                              VestingData
                                                                                                                                              (lam
                                                                                                                                                thunk
                                                                                                                                                Unit
                                                                                                                                                [
                                                                                                                                                  {
                                                                                                                                                    [
                                                                                                                                                      VestingData_match
                                                                                                                                                      ds
                                                                                                                                                    ]
                                                                                                                                                    Bool
                                                                                                                                                  }
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
                                                                                                                                                              PendingTx_match
                                                                                                                                                              [PendingTxIn [[Tuple2 (con bytestring)] (con bytestring)]]
                                                                                                                                                            }
                                                                                                                                                            w
                                                                                                                                                          ]
                                                                                                                                                          Bool
                                                                                                                                                        }
                                                                                                                                                        (lam
                                                                                                                                                          ds
                                                                                                                                                          [List [PendingTxIn [Maybe [[Tuple2 (con bytestring)] (con bytestring)]]]]
                                                                                                                                                          (lam
                                                                                                                                                            ds
                                                                                                                                                            [List PendingTxOut]
                                                                                                                                                            (lam
                                                                                                                                                              ds
                                                                                                                                                              (con integer)
                                                                                                                                                              (lam
                                                                                                                                                                ds
                                                                                                                                                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                                                                (lam
                                                                                                                                                                  ds
                                                                                                                                                                  [PendingTxIn [[Tuple2 (con bytestring)] (con bytestring)]]
                                                                                                                                                                  (lam
                                                                                                                                                                    ds
                                                                                                                                                                    [Interval (con integer)]
                                                                                                                                                                    (lam
                                                                                                                                                                      ds
                                                                                                                                                                      [List [[Tuple2 (con bytestring)] (con bytestring)]]
                                                                                                                                                                      (lam
                                                                                                                                                                        ds
                                                                                                                                                                        (con bytestring)
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
                                                                                                                                                                                ds
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
                                                                                                                                                                                        {
                                                                                                                                                                                          PendingTxIn_match
                                                                                                                                                                                          [[Tuple2 (con bytestring)] (con bytestring)]
                                                                                                                                                                                        }
                                                                                                                                                                                        ds
                                                                                                                                                                                      ]
                                                                                                                                                                                      [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                                                                                    }
                                                                                                                                                                                    (lam
                                                                                                                                                                                      ds
                                                                                                                                                                                      PendingTxOutRef
                                                                                                                                                                                      (lam
                                                                                                                                                                                        ds
                                                                                                                                                                                        [[Tuple2 (con bytestring)] (con bytestring)]
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
                                                                                                                                                                                  [
                                                                                                                                                                                    fAdditiveGroupValue_cscale
                                                                                                                                                                                    fAdditiveGroupValue
                                                                                                                                                                                  ]
                                                                                                                                                                                  [
                                                                                                                                                                                    {
                                                                                                                                                                                      [
                                                                                                                                                                                        {
                                                                                                                                                                                          PendingTxIn_match
                                                                                                                                                                                          [[Tuple2 (con bytestring)] (con bytestring)]
                                                                                                                                                                                        }
                                                                                                                                                                                        ds
                                                                                                                                                                                      ]
                                                                                                                                                                                      [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                                                                                    }
                                                                                                                                                                                    (lam
                                                                                                                                                                                      ww
                                                                                                                                                                                      PendingTxOutRef
                                                                                                                                                                                      (lam
                                                                                                                                                                                        ww
                                                                                                                                                                                        [[Tuple2 (con bytestring)] (con bytestring)]
                                                                                                                                                                                        (lam
                                                                                                                                                                                          ww
                                                                                                                                                                                          [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
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
                                                                                                                                                                                                ww
                                                                                                                                                                                              ]
                                                                                                                                                                                              [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                                                                                            }
                                                                                                                                                                                            (lam
                                                                                                                                                                                              ww
                                                                                                                                                                                              (con bytestring)
                                                                                                                                                                                              (lam
                                                                                                                                                                                                ww
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
                                                                                                                                                                                                        ds
                                                                                                                                                                                                      ]
                                                                                                                                                                                                      ww
                                                                                                                                                                                                    ]
                                                                                                                                                                                                  ]
                                                                                                                                                                                                ]
                                                                                                                                                                                              )
                                                                                                                                                                                            )
                                                                                                                                                                                          ]
                                                                                                                                                                                        )
                                                                                                                                                                                      )
                                                                                                                                                                                    )
                                                                                                                                                                                  ]
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
                                                                                                                                                                                            ds
                                                                                                                                                                                          ]
                                                                                                                                                                                        ]
                                                                                                                                                                                        [
                                                                                                                                                                                          [
                                                                                                                                                                                            availableFrom
                                                                                                                                                                                            ww
                                                                                                                                                                                          ]
                                                                                                                                                                                          ds
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
                                                                                                                                                                                            fMonoidValue_c
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
                                                                                                                                                                                                    {
                                                                                                                                                                                                      PendingTxIn_match
                                                                                                                                                                                                      [[Tuple2 (con bytestring)] (con bytestring)]
                                                                                                                                                                                                    }
                                                                                                                                                                                                    ds
                                                                                                                                                                                                  ]
                                                                                                                                                                                                  (con bytestring)
                                                                                                                                                                                                }
                                                                                                                                                                                                (lam
                                                                                                                                                                                                  ds
                                                                                                                                                                                                  PendingTxOutRef
                                                                                                                                                                                                  (lam
                                                                                                                                                                                                    ds
                                                                                                                                                                                                    [[Tuple2 (con bytestring)] (con bytestring)]
                                                                                                                                                                                                    (lam
                                                                                                                                                                                                      ds
                                                                                                                                                                                                      [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
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
                                                                                                                                                                                                )
                                                                                                                                                                                              ]
                                                                                                                                                                                            ]
                                                                                                                                                                                            ds
                                                                                                                                                                                          ]
                                                                                                                                                                                        ]
                                                                                                                                                                                      ]
                                                                                                                                                                                    ]
                                                                                                                                                                                    [
                                                                                                                                                                                      [
                                                                                                                                                                                        [
                                                                                                                                                                                          unionWith
                                                                                                                                                                                          addInteger
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
                                                                                                                                                                                      [
                                                                                                                                                                                        [
                                                                                                                                                                                          fAdditiveGroupValue_cscale
                                                                                                                                                                                          fAdditiveGroupValue
                                                                                                                                                                                        ]
                                                                                                                                                                                        newAmount
                                                                                                                                                                                      ]
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
                                                                                                                                (termbind
                                                                                                                                  (strict
                                                                                                                                  )
                                                                                                                                  (vardecl
                                                                                                                                    mkValidator
                                                                                                                                    (fun Vesting (fun Data (fun Data (fun [PendingTx [PendingTxIn [[Tuple2 (con bytestring)] (con bytestring)]]] Bool))))
                                                                                                                                  )
                                                                                                                                  (lam
                                                                                                                                    w
                                                                                                                                    Vesting
                                                                                                                                    (lam
                                                                                                                                      w
                                                                                                                                      Data
                                                                                                                                      (lam
                                                                                                                                        w
                                                                                                                                        Data
                                                                                                                                        (lam
                                                                                                                                          w
                                                                                                                                          [PendingTx [PendingTxIn [[Tuple2 (con bytestring)] (con bytestring)]]]
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
                                                                                                                                                    [
                                                                                                                                                      [
                                                                                                                                                        [
                                                                                                                                                          wmkValidator
                                                                                                                                                          ww
                                                                                                                                                        ]
                                                                                                                                                        ww
                                                                                                                                                      ]
                                                                                                                                                      w
                                                                                                                                                    ]
                                                                                                                                                    w
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