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
          (termbind (strict) (vardecl fIsDataFutureData (con integer)) (con 0))
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
                    (vardecl Map (fun [List [[Tuple2 Data] Data]] Data))
                  )
                )
                (let
                  (nonrec)
                  (datatypebind
                    (datatype
                      (tyvardecl FutureData (type))
                      
                      FutureData_match
                      (vardecl
                        FutureData
                        (fun (con bytestring) (fun (con bytestring) (fun (con integer) (fun (con integer) FutureData))))
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
                            fIsDataFutureData_cfromData
                            (fun Data [Maybe FutureData])
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
                                        (fun Unit [Maybe FutureData])
                                      }
                                      (lam
                                        default_arg0
                                        (con bytestring)
                                        (lam thunk Unit { Nothing FutureData })
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
                                                  (fun Unit [Maybe FutureData])
                                                }
                                                (lam
                                                  thunk
                                                  Unit
                                                  { Nothing FutureData }
                                                )
                                              ]
                                              (lam
                                                dl
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
                                                              { Nil_match Data }
                                                              ds
                                                            ]
                                                            (fun Unit [Maybe FutureData])
                                                          }
                                                          (lam
                                                            thunk
                                                            Unit
                                                            {
                                                              Nothing FutureData
                                                            }
                                                          )
                                                        ]
                                                        (lam
                                                          ds
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
                                                                      (fun Unit [Maybe FutureData])
                                                                    }
                                                                    (lam
                                                                      thunk
                                                                      Unit
                                                                      {
                                                                        Nothing
                                                                        FutureData
                                                                      }
                                                                    )
                                                                  ]
                                                                  (lam
                                                                    ml
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
                                                                                (fun Unit [Maybe FutureData])
                                                                              }
                                                                              (lam
                                                                                thunk
                                                                                Unit
                                                                                {
                                                                                  Nothing
                                                                                  FutureData
                                                                                }
                                                                              )
                                                                            ]
                                                                            (lam
                                                                              ms
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
                                                                                          (fun Unit [Maybe FutureData])
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
                                                                                                  (fun Unit [Maybe FutureData])
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
                                                                                                                dl
                                                                                                              ]
                                                                                                              (fun Unit [Maybe FutureData])
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
                                                                                                                      [
                                                                                                                        [
                                                                                                                          {
                                                                                                                            [
                                                                                                                              Data_match
                                                                                                                              ds
                                                                                                                            ]
                                                                                                                            (fun Unit [Maybe FutureData])
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
                                                                                                                                    [
                                                                                                                                      [
                                                                                                                                        {
                                                                                                                                          [
                                                                                                                                            Data_match
                                                                                                                                            ml
                                                                                                                                          ]
                                                                                                                                          (fun Unit [Maybe FutureData])
                                                                                                                                        }
                                                                                                                                        (lam
                                                                                                                                          default_arg0
                                                                                                                                          (con bytestring)
                                                                                                                                          (lam
                                                                                                                                            thunk
                                                                                                                                            Unit
                                                                                                                                            {
                                                                                                                                              Nothing
                                                                                                                                              FutureData
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
                                                                                                                                              FutureData
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
                                                                                                                                          [
                                                                                                                                            [
                                                                                                                                              [
                                                                                                                                                [
                                                                                                                                                  {
                                                                                                                                                    [
                                                                                                                                                      Data_match
                                                                                                                                                      ms
                                                                                                                                                    ]
                                                                                                                                                    (fun Unit [Maybe FutureData])
                                                                                                                                                  }
                                                                                                                                                  (lam
                                                                                                                                                    default_arg0
                                                                                                                                                    (con bytestring)
                                                                                                                                                    (lam
                                                                                                                                                      thunk
                                                                                                                                                      Unit
                                                                                                                                                      {
                                                                                                                                                        Nothing
                                                                                                                                                        FutureData
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
                                                                                                                                                        FutureData
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
                                                                                                                                                      FutureData
                                                                                                                                                    }
                                                                                                                                                    [
                                                                                                                                                      [
                                                                                                                                                        [
                                                                                                                                                          [
                                                                                                                                                            FutureData
                                                                                                                                                            b
                                                                                                                                                          ]
                                                                                                                                                          b
                                                                                                                                                        ]
                                                                                                                                                        i
                                                                                                                                                      ]
                                                                                                                                                      i
                                                                                                                                                    ]
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
                                                                                                                                                  FutureData
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
                                                                                                                                    default_arg0
                                                                                                                                    [List [[Tuple2 Data] Data]]
                                                                                                                                    (lam
                                                                                                                                      thunk
                                                                                                                                      Unit
                                                                                                                                      {
                                                                                                                                        Nothing
                                                                                                                                        FutureData
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
                                                                                                                                FutureData
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
                                                                                                                            FutureData
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
                                                                                                                          FutureData
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
                                                                                                                  FutureData
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
                                                                                                              FutureData
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
                                                                                                            FutureData
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
                                                                                                  FutureData
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
                                                                                              FutureData
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
                                    (lam thunk Unit { Nothing FutureData })
                                  )
                                ]
                                (lam
                                  default_arg0
                                  [List [[Tuple2 Data] Data]]
                                  (lam thunk Unit { Nothing FutureData })
                                )
                              ]
                              Unit
                            ]
                          )
                        )
                        (let
                          (nonrec)
                          (datatypebind
                            (datatype
                              (tyvardecl OracleValue (fun (type) (type)))
                              (tyvardecl a (type))
                              OracleValue_match
                              (vardecl
                                OracleValue
                                (fun (con bytestring) (fun (con integer) (fun a [OracleValue a])))
                              )
                            )
                          )
                          (let
                            (nonrec)
                            (datatypebind
                              (datatype
                                (tyvardecl FutureRedeemer (type))
                                
                                FutureRedeemer_match
                                (vardecl AdjustMargin FutureRedeemer)
                                (vardecl
                                  Settle
                                  (fun [OracleValue (con integer)] FutureRedeemer)
                                )
                              )
                            )
                            (let
                              (nonrec)
                              (termbind
                                (strict)
                                (vardecl
                                  fIsDataFutureRedeemer_cfromData
                                  (fun Data [Maybe FutureRedeemer])
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
                                              (fun Unit [Maybe FutureRedeemer])
                                            }
                                            (lam
                                              default_arg0
                                              (con bytestring)
                                              (lam
                                                thunk
                                                Unit
                                                { Nothing FutureRedeemer }
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
                                                          { Nil_match Data } ds
                                                        ]
                                                        (fun Unit [Maybe FutureRedeemer])
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
                                                                    (con 0)
                                                                  ]
                                                                ]
                                                                (fun Unit [Maybe FutureRedeemer])
                                                              }
                                                              (lam
                                                                thunk
                                                                Unit
                                                                [
                                                                  {
                                                                    Just
                                                                    FutureRedeemer
                                                                  }
                                                                  AdjustMargin
                                                                ]
                                                              )
                                                            ]
                                                            (lam
                                                              thunk
                                                              Unit
                                                              {
                                                                Nothing
                                                                FutureRedeemer
                                                              }
                                                            )
                                                          ]
                                                          Unit
                                                        ]
                                                      )
                                                    ]
                                                    (lam
                                                      o
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
                                                                  (fun Unit [Maybe FutureRedeemer])
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
                                                                          (fun Unit [Maybe FutureRedeemer])
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
                                                                                        o
                                                                                      ]
                                                                                      (fun Unit [Maybe FutureRedeemer])
                                                                                    }
                                                                                    (lam
                                                                                      default_arg0
                                                                                      (con bytestring)
                                                                                      (lam
                                                                                        thunk
                                                                                        Unit
                                                                                        {
                                                                                          Nothing
                                                                                          FutureRedeemer
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
                                                                                                (fun Unit [Maybe FutureRedeemer])
                                                                                              }
                                                                                              (lam
                                                                                                thunk
                                                                                                Unit
                                                                                                {
                                                                                                  Nothing
                                                                                                  FutureRedeemer
                                                                                                }
                                                                                              )
                                                                                            ]
                                                                                            (lam
                                                                                              sig
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
                                                                                                          (fun Unit [Maybe FutureRedeemer])
                                                                                                        }
                                                                                                        (lam
                                                                                                          thunk
                                                                                                          Unit
                                                                                                          {
                                                                                                            Nothing
                                                                                                            FutureRedeemer
                                                                                                          }
                                                                                                        )
                                                                                                      ]
                                                                                                      (lam
                                                                                                        s
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
                                                                                                                    (fun Unit [Maybe FutureRedeemer])
                                                                                                                  }
                                                                                                                  (lam
                                                                                                                    thunk
                                                                                                                    Unit
                                                                                                                    {
                                                                                                                      Nothing
                                                                                                                      FutureRedeemer
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
                                                                                                                              (fun Unit [Maybe FutureRedeemer])
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
                                                                                                                                          fIsDataFutureData
                                                                                                                                        ]
                                                                                                                                      ]
                                                                                                                                      (fun Unit [Maybe FutureRedeemer])
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
                                                                                                                                                    sig
                                                                                                                                                  ]
                                                                                                                                                  (fun Unit [Maybe FutureRedeemer])
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
                                                                                                                                                          [
                                                                                                                                                            [
                                                                                                                                                              {
                                                                                                                                                                [
                                                                                                                                                                  Data_match
                                                                                                                                                                  s
                                                                                                                                                                ]
                                                                                                                                                                (fun Unit [Maybe FutureRedeemer])
                                                                                                                                                              }
                                                                                                                                                              (lam
                                                                                                                                                                default_arg0
                                                                                                                                                                (con bytestring)
                                                                                                                                                                (lam
                                                                                                                                                                  thunk
                                                                                                                                                                  Unit
                                                                                                                                                                  {
                                                                                                                                                                    Nothing
                                                                                                                                                                    FutureRedeemer
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
                                                                                                                                                                    FutureRedeemer
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
                                                                                                                                                                [
                                                                                                                                                                  [
                                                                                                                                                                    [
                                                                                                                                                                      [
                                                                                                                                                                        {
                                                                                                                                                                          [
                                                                                                                                                                            Data_match
                                                                                                                                                                            v
                                                                                                                                                                          ]
                                                                                                                                                                          (fun Unit [Maybe FutureRedeemer])
                                                                                                                                                                        }
                                                                                                                                                                        (lam
                                                                                                                                                                          default_arg0
                                                                                                                                                                          (con bytestring)
                                                                                                                                                                          (lam
                                                                                                                                                                            thunk
                                                                                                                                                                            Unit
                                                                                                                                                                            {
                                                                                                                                                                              Nothing
                                                                                                                                                                              FutureRedeemer
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
                                                                                                                                                                              FutureRedeemer
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
                                                                                                                                                                            FutureRedeemer
                                                                                                                                                                          }
                                                                                                                                                                          [
                                                                                                                                                                            Settle
                                                                                                                                                                            [
                                                                                                                                                                              [
                                                                                                                                                                                [
                                                                                                                                                                                  {
                                                                                                                                                                                    OracleValue
                                                                                                                                                                                    (con integer)
                                                                                                                                                                                  }
                                                                                                                                                                                  b
                                                                                                                                                                                ]
                                                                                                                                                                                i
                                                                                                                                                                              ]
                                                                                                                                                                              i
                                                                                                                                                                            ]
                                                                                                                                                                          ]
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
                                                                                                                                                                        FutureRedeemer
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
                                                                                                                                                          default_arg0
                                                                                                                                                          [List [[Tuple2 Data] Data]]
                                                                                                                                                          (lam
                                                                                                                                                            thunk
                                                                                                                                                            Unit
                                                                                                                                                            {
                                                                                                                                                              Nothing
                                                                                                                                                              FutureRedeemer
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
                                                                                                                                                      FutureRedeemer
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
                                                                                                                                                  FutureRedeemer
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
                                                                                                                                                FutureRedeemer
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
                                                                                                                                      FutureRedeemer
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
                                                                                                                                  FutureRedeemer
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
                                                                                      FutureRedeemer
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
                                                                                    FutureRedeemer
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
                                                                          FutureRedeemer
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
                                                                      FutureRedeemer
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
                                        (lam
                                          default_arg0
                                          (con integer)
                                          (lam
                                            thunk
                                            Unit
                                            { Nothing FutureRedeemer }
                                          )
                                        )
                                      ]
                                      (lam
                                        default_arg0
                                        [List [[Tuple2 Data] Data]]
                                        (lam
                                          thunk Unit { Nothing FutureRedeemer }
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
                                  (builtin addInteger)
                                )
                                (let
                                  (nonrec)
                                  (datatypebind
                                    (datatype
                                      (tyvardecl
                                        These (fun (type) (fun (type) (type)))
                                      )
                                      (tyvardecl a (type)) (tyvardecl b (type))
                                      These_match
                                      (vardecl That (fun b [[These a] b]))
                                      (vardecl
                                        These (fun a (fun b [[These a] b]))
                                      )
                                      (vardecl This (fun a [[These a] b]))
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
                                                          [ { Nil_match a } l ]
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
                                                                        foldr a
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
                                                                        (nonrec)
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
                                                                        (rec)
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
                                                                          go ds
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
                                          (nonrec)
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
                                            (nonrec)
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
                                                        [ [ unionVal ls ] rs ]
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
                                                  fMonoidValue_c
                                                  (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]))
                                                )
                                                [ unionWith addInteger ]
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
                                                      (tyvardecl
                                                        PendingTxOut (type)
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
                                                            Extended
                                                            (fun (type) (type))
                                                          )
                                                          (tyvardecl a (type))
                                                          Extended_match
                                                          (vardecl
                                                            Finite
                                                            (fun a [Extended a])
                                                          )
                                                          (vardecl
                                                            NegInf [Extended a]
                                                          )
                                                          (vardecl
                                                            PosInf [Extended a]
                                                          )
                                                        )
                                                      )
                                                      (let
                                                        (nonrec)
                                                        (datatypebind
                                                          (datatype
                                                            (tyvardecl
                                                              LowerBound
                                                              (fun (type) (type))
                                                            )
                                                            (tyvardecl a (type))
                                                            LowerBound_match
                                                            (vardecl
                                                              LowerBound
                                                              (fun [Extended a] (fun Bool [LowerBound a]))
                                                            )
                                                          )
                                                        )
                                                        (let
                                                          (nonrec)
                                                          (datatypebind
                                                            (datatype
                                                              (tyvardecl
                                                                UpperBound
                                                                (fun (type) (type))
                                                              )
                                                              (tyvardecl
                                                                a (type)
                                                              )
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
                                                                (tyvardecl
                                                                  Interval
                                                                  (fun (type) (type))
                                                                )
                                                                (tyvardecl
                                                                  a (type)
                                                                )
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
                                                                      (fun (type) (type))
                                                                    )
                                                                    (tyvardecl
                                                                      w (type)
                                                                    )
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
                                                                      (tyvardecl
                                                                        PendingTx
                                                                        (fun (type) (type))
                                                                      )
                                                                      (tyvardecl
                                                                        i (type)
                                                                      )
                                                                      PendingTx_match
                                                                      (vardecl
                                                                        PendingTx
                                                                        (fun [List [PendingTxIn [Maybe [[Tuple2 (con bytestring)] (con bytestring)]]]] (fun [List PendingTxOut] (fun (con integer) (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun i (fun [Interval (con integer)] (fun [List [[Tuple2 (con bytestring)] (con bytestring)]] (fun (con bytestring) [PendingTx i]))))))))
                                                                      )
                                                                    )
                                                                  )
                                                                  (let
                                                                    (nonrec)
                                                                    (termbind
                                                                      (strict)
                                                                      (vardecl
                                                                        emptyByteString
                                                                        (con bytestring)
                                                                      )
                                                                      (con #)
                                                                    )
                                                                    (let
                                                                      (nonrec)
                                                                      (termbind
                                                                        (strict)
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
                                                                        (nonrec)
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
                                                                          (nonrec
                                                                          )
                                                                          (termbind
                                                                            (strict
                                                                            )
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
                                                                                        greaterThanInteger
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
                                                                                            lessThanInteger
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
                                                                                      multiplyInteger
                                                                                      (fun (con integer) (fun (con integer) (con integer)))
                                                                                    )
                                                                                    (builtin
                                                                                      multiplyInteger
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
                                                                                                  (nonrec
                                                                                                  )
                                                                                                  (termbind
                                                                                                    (strict
                                                                                                    )
                                                                                                    (vardecl
                                                                                                      j
                                                                                                      (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)] (con integer))
                                                                                                    )
                                                                                                    (lam
                                                                                                      i
                                                                                                      [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]
                                                                                                      (let
                                                                                                        (rec
                                                                                                        )
                                                                                                        (termbind
                                                                                                          (strict
                                                                                                          )
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
                                                                                                                (con
                                                                                                                  0
                                                                                                                )
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
                                                                                                                        [
                                                                                                                          [
                                                                                                                            [
                                                                                                                              {
                                                                                                                                [
                                                                                                                                  Bool_match
                                                                                                                                  [
                                                                                                                                    [
                                                                                                                                      equalsByteString
                                                                                                                                      c
                                                                                                                                    ]
                                                                                                                                    tn
                                                                                                                                  ]
                                                                                                                                ]
                                                                                                                                (fun Unit (con integer))
                                                                                                                              }
                                                                                                                              (lam
                                                                                                                                thunk
                                                                                                                                Unit
                                                                                                                                i
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
                                                                                                            ]
                                                                                                          )
                                                                                                        )
                                                                                                        [
                                                                                                          go
                                                                                                          i
                                                                                                        ]
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
                                                                                                            (con
                                                                                                              0
                                                                                                            )
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
                                                                                                                    [
                                                                                                                      [
                                                                                                                        [
                                                                                                                          {
                                                                                                                            [
                                                                                                                              Bool_match
                                                                                                                              [
                                                                                                                                [
                                                                                                                                  equalsByteString
                                                                                                                                  c
                                                                                                                                ]
                                                                                                                                cur
                                                                                                                              ]
                                                                                                                            ]
                                                                                                                            (fun Unit (con integer))
                                                                                                                          }
                                                                                                                          (lam
                                                                                                                            thunk
                                                                                                                            Unit
                                                                                                                            [
                                                                                                                              j
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
                                                                                                        ]
                                                                                                      )
                                                                                                    )
                                                                                                    [
                                                                                                      go
                                                                                                      ds
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
                                                                                              wmkValidator
                                                                                              (fun (con integer) (fun (con integer) (fun (con integer) (fun (con bytestring) (fun (con integer) (fun Data (fun Data (fun [PendingTx [PendingTxIn [[Tuple2 (con bytestring)] (con bytestring)]]] Bool))))))))
                                                                                            )
                                                                                            (lam
                                                                                              ww
                                                                                              (con integer)
                                                                                              (lam
                                                                                                ww
                                                                                                (con integer)
                                                                                                (lam
                                                                                                  ww
                                                                                                  (con integer)
                                                                                                  (lam
                                                                                                    ww
                                                                                                    (con bytestring)
                                                                                                    (lam
                                                                                                      ww
                                                                                                      (con integer)
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
                                                                                                              [
                                                                                                                [
                                                                                                                  {
                                                                                                                    [
                                                                                                                      {
                                                                                                                        Maybe_match
                                                                                                                        FutureData
                                                                                                                      }
                                                                                                                      [
                                                                                                                        fIsDataFutureData_cfromData
                                                                                                                        w
                                                                                                                      ]
                                                                                                                    ]
                                                                                                                    (fun Unit Bool)
                                                                                                                  }
                                                                                                                  (lam
                                                                                                                    ds
                                                                                                                    FutureData
                                                                                                                    (lam
                                                                                                                      thunk
                                                                                                                      Unit
                                                                                                                      [
                                                                                                                        {
                                                                                                                          [
                                                                                                                            FutureData_match
                                                                                                                            ds
                                                                                                                          ]
                                                                                                                          Bool
                                                                                                                        }
                                                                                                                        (lam
                                                                                                                          ds
                                                                                                                          (con bytestring)
                                                                                                                          (lam
                                                                                                                            ds
                                                                                                                            (con bytestring)
                                                                                                                            (lam
                                                                                                                              ds
                                                                                                                              (con integer)
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
                                                                                                                                            FutureRedeemer
                                                                                                                                          }
                                                                                                                                          [
                                                                                                                                            fIsDataFutureRedeemer_cfromData
                                                                                                                                            w
                                                                                                                                          ]
                                                                                                                                        ]
                                                                                                                                        (fun Unit Bool)
                                                                                                                                      }
                                                                                                                                      (lam
                                                                                                                                        r
                                                                                                                                        FutureRedeemer
                                                                                                                                        (lam
                                                                                                                                          thunk
                                                                                                                                          Unit
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
                                                                                                                                                                (strict
                                                                                                                                                                )
                                                                                                                                                                (vardecl
                                                                                                                                                                  paidOutTo
                                                                                                                                                                  (fun (con integer) (fun (con bytestring) (fun PendingTxOut Bool)))
                                                                                                                                                                )
                                                                                                                                                                (lam
                                                                                                                                                                  vl
                                                                                                                                                                  (con integer)
                                                                                                                                                                  (lam
                                                                                                                                                                    pk
                                                                                                                                                                    (con bytestring)
                                                                                                                                                                    (lam
                                                                                                                                                                      txo
                                                                                                                                                                      PendingTxOut
                                                                                                                                                                      [
                                                                                                                                                                        {
                                                                                                                                                                          [
                                                                                                                                                                            PendingTxOut_match
                                                                                                                                                                            txo
                                                                                                                                                                          ]
                                                                                                                                                                          Bool
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
                                                                                                                                                                                        PendingTxOutType_match
                                                                                                                                                                                        ds
                                                                                                                                                                                      ]
                                                                                                                                                                                      (fun Unit Bool)
                                                                                                                                                                                    }
                                                                                                                                                                                    (lam
                                                                                                                                                                                      thunk
                                                                                                                                                                                      Unit
                                                                                                                                                                                      False
                                                                                                                                                                                    )
                                                                                                                                                                                  ]
                                                                                                                                                                                  (lam
                                                                                                                                                                                    pk
                                                                                                                                                                                    (con bytestring)
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
                                                                                                                                                                                                    equalsByteString
                                                                                                                                                                                                    pk
                                                                                                                                                                                                  ]
                                                                                                                                                                                                  pk
                                                                                                                                                                                                ]
                                                                                                                                                                                              ]
                                                                                                                                                                                              (fun Unit Bool)
                                                                                                                                                                                            }
                                                                                                                                                                                            (lam
                                                                                                                                                                                              thunk
                                                                                                                                                                                              Unit
                                                                                                                                                                                              [
                                                                                                                                                                                                [
                                                                                                                                                                                                  equalsInteger
                                                                                                                                                                                                  vl
                                                                                                                                                                                                ]
                                                                                                                                                                                                [
                                                                                                                                                                                                  [
                                                                                                                                                                                                    [
                                                                                                                                                                                                      valueOf
                                                                                                                                                                                                      ds
                                                                                                                                                                                                    ]
                                                                                                                                                                                                    emptyByteString
                                                                                                                                                                                                  ]
                                                                                                                                                                                                  emptyByteString
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
                                                                                                                                                              )
                                                                                                                                                              [
                                                                                                                                                                [
                                                                                                                                                                  [
                                                                                                                                                                    {
                                                                                                                                                                      [
                                                                                                                                                                        FutureRedeemer_match
                                                                                                                                                                        r
                                                                                                                                                                      ]
                                                                                                                                                                      (fun Unit Bool)
                                                                                                                                                                    }
                                                                                                                                                                    (lam
                                                                                                                                                                      thunk
                                                                                                                                                                      Unit
                                                                                                                                                                      [
                                                                                                                                                                        [
                                                                                                                                                                          greaterThanInteger
                                                                                                                                                                          [
                                                                                                                                                                            [
                                                                                                                                                                              [
                                                                                                                                                                                valueOf
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
                                                                                                                                                                              emptyByteString
                                                                                                                                                                            ]
                                                                                                                                                                            emptyByteString
                                                                                                                                                                          ]
                                                                                                                                                                        ]
                                                                                                                                                                        [
                                                                                                                                                                          [
                                                                                                                                                                            addInteger
                                                                                                                                                                            ds
                                                                                                                                                                          ]
                                                                                                                                                                          ds
                                                                                                                                                                        ]
                                                                                                                                                                      ]
                                                                                                                                                                    )
                                                                                                                                                                  ]
                                                                                                                                                                  (lam
                                                                                                                                                                    ov
                                                                                                                                                                    [OracleValue (con integer)]
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
                                                                                                                                                                            spotPrice
                                                                                                                                                                            (con integer)
                                                                                                                                                                          )
                                                                                                                                                                          [
                                                                                                                                                                            {
                                                                                                                                                                              [
                                                                                                                                                                                {
                                                                                                                                                                                  OracleValue_match
                                                                                                                                                                                  (con integer)
                                                                                                                                                                                }
                                                                                                                                                                                ov
                                                                                                                                                                              ]
                                                                                                                                                                              (con integer)
                                                                                                                                                                            }
                                                                                                                                                                            (lam
                                                                                                                                                                              pk
                                                                                                                                                                              (con bytestring)
                                                                                                                                                                              (lam
                                                                                                                                                                                h
                                                                                                                                                                                (con integer)
                                                                                                                                                                                (lam
                                                                                                                                                                                  t
                                                                                                                                                                                  (con integer)
                                                                                                                                                                                  [
                                                                                                                                                                                    [
                                                                                                                                                                                      [
                                                                                                                                                                                        {
                                                                                                                                                                                          [
                                                                                                                                                                                            Bool_match
                                                                                                                                                                                            [
                                                                                                                                                                                              [
                                                                                                                                                                                                equalsByteString
                                                                                                                                                                                                pk
                                                                                                                                                                                              ]
                                                                                                                                                                                              ww
                                                                                                                                                                                            ]
                                                                                                                                                                                          ]
                                                                                                                                                                                          (fun Unit (con integer))
                                                                                                                                                                                        }
                                                                                                                                                                                        (lam
                                                                                                                                                                                          thunk
                                                                                                                                                                                          Unit
                                                                                                                                                                                          t
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
                                                                                                                                                                                                  (con integer)
                                                                                                                                                                                                }
                                                                                                                                                                                                (con integer)
                                                                                                                                                                                              }
                                                                                                                                                                                              [
                                                                                                                                                                                                {
                                                                                                                                                                                                  error
                                                                                                                                                                                                  [[Tuple2 (con integer)] (con integer)]
                                                                                                                                                                                                }
                                                                                                                                                                                                Unit
                                                                                                                                                                                              ]
                                                                                                                                                                                            ]
                                                                                                                                                                                            (con integer)
                                                                                                                                                                                          }
                                                                                                                                                                                          (lam
                                                                                                                                                                                            ds
                                                                                                                                                                                            (con integer)
                                                                                                                                                                                            (lam
                                                                                                                                                                                              b
                                                                                                                                                                                              (con integer)
                                                                                                                                                                                              b
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
                                                                                                                                                                        )
                                                                                                                                                                        (let
                                                                                                                                                                          (nonrec
                                                                                                                                                                          )
                                                                                                                                                                          (termbind
                                                                                                                                                                            (nonstrict
                                                                                                                                                                            )
                                                                                                                                                                            (vardecl
                                                                                                                                                                              delta
                                                                                                                                                                              (con integer)
                                                                                                                                                                            )
                                                                                                                                                                            [
                                                                                                                                                                              [
                                                                                                                                                                                multiplyInteger
                                                                                                                                                                                ww
                                                                                                                                                                              ]
                                                                                                                                                                              [
                                                                                                                                                                                [
                                                                                                                                                                                  subtractInteger
                                                                                                                                                                                  spotPrice
                                                                                                                                                                                ]
                                                                                                                                                                                ww
                                                                                                                                                                              ]
                                                                                                                                                                            ]
                                                                                                                                                                          )
                                                                                                                                                                          (let
                                                                                                                                                                            (nonrec
                                                                                                                                                                            )
                                                                                                                                                                            (termbind
                                                                                                                                                                              (nonstrict
                                                                                                                                                                              )
                                                                                                                                                                              (vardecl
                                                                                                                                                                                expShort
                                                                                                                                                                                (con integer)
                                                                                                                                                                              )
                                                                                                                                                                              [
                                                                                                                                                                                [
                                                                                                                                                                                  subtractInteger
                                                                                                                                                                                  ds
                                                                                                                                                                                ]
                                                                                                                                                                                delta
                                                                                                                                                                              ]
                                                                                                                                                                            )
                                                                                                                                                                            (let
                                                                                                                                                                              (nonrec
                                                                                                                                                                              )
                                                                                                                                                                              (termbind
                                                                                                                                                                                (nonstrict
                                                                                                                                                                                )
                                                                                                                                                                                (vardecl
                                                                                                                                                                                  expLong
                                                                                                                                                                                  (con integer)
                                                                                                                                                                                )
                                                                                                                                                                                [
                                                                                                                                                                                  [
                                                                                                                                                                                    addInteger
                                                                                                                                                                                    ds
                                                                                                                                                                                  ]
                                                                                                                                                                                  delta
                                                                                                                                                                                ]
                                                                                                                                                                              )
                                                                                                                                                                              [
                                                                                                                                                                                [
                                                                                                                                                                                  [
                                                                                                                                                                                    {
                                                                                                                                                                                      [
                                                                                                                                                                                        {
                                                                                                                                                                                          Nil_match
                                                                                                                                                                                          PendingTxOut
                                                                                                                                                                                        }
                                                                                                                                                                                        ds
                                                                                                                                                                                      ]
                                                                                                                                                                                      (fun Unit Bool)
                                                                                                                                                                                    }
                                                                                                                                                                                    (lam
                                                                                                                                                                                      thunk
                                                                                                                                                                                      Unit
                                                                                                                                                                                      False
                                                                                                                                                                                    )
                                                                                                                                                                                  ]
                                                                                                                                                                                  (lam
                                                                                                                                                                                    o
                                                                                                                                                                                    PendingTxOut
                                                                                                                                                                                    (lam
                                                                                                                                                                                      ds
                                                                                                                                                                                      [List PendingTxOut]
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
                                                                                                                                                                                                    PendingTxOut
                                                                                                                                                                                                  }
                                                                                                                                                                                                  ds
                                                                                                                                                                                                ]
                                                                                                                                                                                                (fun Unit Bool)
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
                                                                                                                                                                                                      reqMargin
                                                                                                                                                                                                      (con integer)
                                                                                                                                                                                                    )
                                                                                                                                                                                                    [
                                                                                                                                                                                                      [
                                                                                                                                                                                                        addInteger
                                                                                                                                                                                                        ww
                                                                                                                                                                                                      ]
                                                                                                                                                                                                      [
                                                                                                                                                                                                        [
                                                                                                                                                                                                          multiplyInteger
                                                                                                                                                                                                          ww
                                                                                                                                                                                                        ]
                                                                                                                                                                                                        [
                                                                                                                                                                                                          [
                                                                                                                                                                                                            subtractInteger
                                                                                                                                                                                                            spotPrice
                                                                                                                                                                                                          ]
                                                                                                                                                                                                          ww
                                                                                                                                                                                                        ]
                                                                                                                                                                                                      ]
                                                                                                                                                                                                    ]
                                                                                                                                                                                                  )
                                                                                                                                                                                                  (let
                                                                                                                                                                                                    (nonrec
                                                                                                                                                                                                    )
                                                                                                                                                                                                    (termbind
                                                                                                                                                                                                      (nonstrict
                                                                                                                                                                                                      )
                                                                                                                                                                                                      (vardecl
                                                                                                                                                                                                        totalMargin
                                                                                                                                                                                                        (con integer)
                                                                                                                                                                                                      )
                                                                                                                                                                                                      [
                                                                                                                                                                                                        [
                                                                                                                                                                                                          addInteger
                                                                                                                                                                                                          ds
                                                                                                                                                                                                        ]
                                                                                                                                                                                                        ds
                                                                                                                                                                                                      ]
                                                                                                                                                                                                    )
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
                                                                                                                                                                                                        [
                                                                                                                                                                                                          [
                                                                                                                                                                                                            [
                                                                                                                                                                                                              {
                                                                                                                                                                                                                [
                                                                                                                                                                                                                  Bool_match
                                                                                                                                                                                                                  [
                                                                                                                                                                                                                    [
                                                                                                                                                                                                                      lessThanInteger
                                                                                                                                                                                                                      ds
                                                                                                                                                                                                                    ]
                                                                                                                                                                                                                    reqMargin
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
                                                                                                                                                                                                                      paidOutTo
                                                                                                                                                                                                                      totalMargin
                                                                                                                                                                                                                    ]
                                                                                                                                                                                                                    ds
                                                                                                                                                                                                                  ]
                                                                                                                                                                                                                  o
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
                                                                                                                                                                                                      [
                                                                                                                                                                                                        [
                                                                                                                                                                                                          [
                                                                                                                                                                                                            {
                                                                                                                                                                                                              [
                                                                                                                                                                                                                Bool_match
                                                                                                                                                                                                                [
                                                                                                                                                                                                                  [
                                                                                                                                                                                                                    lessThanInteger
                                                                                                                                                                                                                    ds
                                                                                                                                                                                                                  ]
                                                                                                                                                                                                                  reqMargin
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
                                                                                                                                                                                                                              paidOutTo
                                                                                                                                                                                                                              totalMargin
                                                                                                                                                                                                                            ]
                                                                                                                                                                                                                            ds
                                                                                                                                                                                                                          ]
                                                                                                                                                                                                                          o
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
                                                                                                                                                                                                                    j
                                                                                                                                                                                                                  )
                                                                                                                                                                                                                ]
                                                                                                                                                                                                                Unit
                                                                                                                                                                                                              ]
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
                                                                                                                                                                                                  )
                                                                                                                                                                                                )
                                                                                                                                                                                              )
                                                                                                                                                                                            ]
                                                                                                                                                                                            (lam
                                                                                                                                                                                              o
                                                                                                                                                                                              PendingTxOut
                                                                                                                                                                                              (lam
                                                                                                                                                                                                ds
                                                                                                                                                                                                [List PendingTxOut]
                                                                                                                                                                                                (lam
                                                                                                                                                                                                  thunk
                                                                                                                                                                                                  Unit
                                                                                                                                                                                                  [
                                                                                                                                                                                                    {
                                                                                                                                                                                                      [
                                                                                                                                                                                                        {
                                                                                                                                                                                                          Interval_match
                                                                                                                                                                                                          (con integer)
                                                                                                                                                                                                        }
                                                                                                                                                                                                        ds
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
                                                                                                                                                                                                                      [
                                                                                                                                                                                                                        [
                                                                                                                                                                                                                          [
                                                                                                                                                                                                                            {
                                                                                                                                                                                                                              [
                                                                                                                                                                                                                                Bool_match
                                                                                                                                                                                                                                [
                                                                                                                                                                                                                                  [
                                                                                                                                                                                                                                    [
                                                                                                                                                                                                                                      paidOutTo
                                                                                                                                                                                                                                      expShort
                                                                                                                                                                                                                                    ]
                                                                                                                                                                                                                                    ds
                                                                                                                                                                                                                                  ]
                                                                                                                                                                                                                                  o
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
                                                                                                                                                                                                                                    paidOutTo
                                                                                                                                                                                                                                    expLong
                                                                                                                                                                                                                                  ]
                                                                                                                                                                                                                                  ds
                                                                                                                                                                                                                                ]
                                                                                                                                                                                                                                o
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
                                                                                                                                                                                                                    [
                                                                                                                                                                                                                      [
                                                                                                                                                                                                                        [
                                                                                                                                                                                                                          {
                                                                                                                                                                                                                            [
                                                                                                                                                                                                                              Bool_match
                                                                                                                                                                                                                              [
                                                                                                                                                                                                                                [
                                                                                                                                                                                                                                  [
                                                                                                                                                                                                                                    paidOutTo
                                                                                                                                                                                                                                    expShort
                                                                                                                                                                                                                                  ]
                                                                                                                                                                                                                                  ds
                                                                                                                                                                                                                                ]
                                                                                                                                                                                                                                o
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
                                                                                                                                                                                                                                            paidOutTo
                                                                                                                                                                                                                                            expLong
                                                                                                                                                                                                                                          ]
                                                                                                                                                                                                                                          ds
                                                                                                                                                                                                                                        ]
                                                                                                                                                                                                                                        o
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
                                                                                                                                                                                                                                  j
                                                                                                                                                                                                                                )
                                                                                                                                                                                                                              ]
                                                                                                                                                                                                                              Unit
                                                                                                                                                                                                                            ]
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
                                                                                                                                                                                                                )
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
                                                                                                                                                                                                                    [
                                                                                                                                                                                                                      {
                                                                                                                                                                                                                        [
                                                                                                                                                                                                                          {
                                                                                                                                                                                                                            UpperBound_match
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
                                                                                                                                                                                                                                                    ww
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
                                                                                                                                                                                                                              (lam
                                                                                                                                                                                                                                thunk
                                                                                                                                                                                                                                Unit
                                                                                                                                                                                                                                j
                                                                                                                                                                                                                              )
                                                                                                                                                                                                                            ]
                                                                                                                                                                                                                            Unit
                                                                                                                                                                                                                          ]
                                                                                                                                                                                                                        )
                                                                                                                                                                                                                      )
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
                                                                                                                                                                                                                                          ww
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
                                                                                                                                                                                                                                                ww
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
                                                                                                                                                                                                                                ]
                                                                                                                                                                                                                                Unit
                                                                                                                                                                                                                              ]
                                                                                                                                                                                                                            )
                                                                                                                                                                                                                          )
                                                                                                                                                                                                                        ]
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
                                                                                                  Future
                                                                                                  (type)
                                                                                                )
                                                                                                
                                                                                                Future_match
                                                                                                (vardecl
                                                                                                  Future
                                                                                                  (fun (con integer) (fun (con integer) (fun (con integer) (fun (con integer) (fun (con bytestring) (fun (con integer) Future))))))
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
                                                                                                  (fun Future (fun Data (fun Data (fun [PendingTx [PendingTxIn [[Tuple2 (con bytestring)] (con bytestring)]]] Bool))))
                                                                                                )
                                                                                                (lam
                                                                                                  w
                                                                                                  Future
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
                                                                                                              Future_match
                                                                                                              w
                                                                                                            ]
                                                                                                            Bool
                                                                                                          }
                                                                                                          (lam
                                                                                                            ww
                                                                                                            (con integer)
                                                                                                            (lam
                                                                                                              ww
                                                                                                              (con integer)
                                                                                                              (lam
                                                                                                                ww
                                                                                                                (con integer)
                                                                                                                (lam
                                                                                                                  ww
                                                                                                                  (con integer)
                                                                                                                  (lam
                                                                                                                    ww
                                                                                                                    (con bytestring)
                                                                                                                    (lam
                                                                                                                      ww
                                                                                                                      (con integer)
                                                                                                                      [
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