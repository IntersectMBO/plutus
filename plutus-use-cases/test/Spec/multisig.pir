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
          (datatype (tyvardecl Unit (type))  Unit_match (vardecl Unit Unit))
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
              (vardecl
                addInteger (fun (con integer) (fun (con integer) (con integer)))
              )
              (builtin addInteger)
            )
            (let
              (nonrec)
              (termbind
                (strict)
                (vardecl length (all a (type) (fun [List a] (con integer))))
                (abs
                  a
                  (type)
                  (lam
                    as
                    [List a]
                    [
                      [
                        [
                          { { foldr a } (con integer) }
                          (lam
                            ds
                            a
                            (lam
                              acc (con integer) [ [ addInteger acc ] (con 1) ]
                            )
                          )
                        ]
                        (con 0)
                      ]
                      as
                    ]
                  )
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
                    (vardecl charToString (fun (con integer) (con string)))
                    (builtin charToString)
                  )
                  (let
                    (nonrec)
                    (termbind (strict) (vardecl emptyString (con string)) (con )
                    )
                    (let
                      (rec)
                      (termbind
                        (strict)
                        (vardecl
                          toPlutusString (fun [List (con integer)] (con string))
                        )
                        (lam
                          str
                          [List (con integer)]
                          [
                            [
                              [
                                {
                                  [ { Nil_match (con integer) } str ]
                                  (fun Unit (con string))
                                }
                                (lam thunk Unit emptyString)
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
                                      [ appendString [ charToString c ] ]
                                      [ toPlutusString rest ]
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
                        (datatypebind
                          (datatype
                            (tyvardecl Bool (type))
                            
                            Bool_match
                            (vardecl True Bool) (vardecl False Bool)
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
                                  [ [ (builtin equalsByteString) arg ] arg ]
                                ]
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
                                (vardecl trace (fun (con string) Unit))
                                (lam
                                  arg
                                  (con string)
                                  [
                                    (lam b (all a (type) (fun a a)) Unit)
                                    [ (builtin trace) arg ]
                                  ]
                                )
                              )
                              (let
                                (nonrec)
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
                                            (all a (type) (fun a (fun a a)))
                                            [ [ { b Bool } True ] False ]
                                          )
                                          [
                                            [
                                              [ (builtin verifySignature) arg ]
                                              arg
                                            ]
                                            arg
                                          ]
                                        ]
                                      )
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
                                        (tyvardecl Interval (fun (type) (type)))
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
                                      (termbind
                                        (strict)
                                        (vardecl
                                          wtxSignedBy
                                          (fun [List [[Tuple2 (con bytestring)] (con bytestring)]] (fun (con bytestring) (fun (con bytestring) Bool)))
                                        )
                                        (lam
                                          ww
                                          [List [[Tuple2 (con bytestring)] (con bytestring)]]
                                          (lam
                                            ww
                                            (con bytestring)
                                            (lam
                                              w
                                              (con bytestring)
                                              (let
                                                (rec)
                                                (termbind
                                                  (strict)
                                                  (vardecl
                                                    go
                                                    (fun [List [[Tuple2 (con bytestring)] (con bytestring)]] Bool)
                                                  )
                                                  (lam
                                                    l
                                                    [List [[Tuple2 (con bytestring)] (con bytestring)]]
                                                    [
                                                      [
                                                        [
                                                          {
                                                            [
                                                              {
                                                                Nil_match
                                                                [[Tuple2 (con bytestring)] (con bytestring)]
                                                              }
                                                              l
                                                            ]
                                                            (fun Unit Bool)
                                                          }
                                                          (lam thunk Unit False)
                                                        ]
                                                        (lam
                                                          ds
                                                          [[Tuple2 (con bytestring)] (con bytestring)]
                                                          (lam
                                                            r
                                                            [List [[Tuple2 (con bytestring)] (con bytestring)]]
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
                                                                  Bool
                                                                }
                                                                (lam
                                                                  pk
                                                                  (con bytestring)
                                                                  (lam
                                                                    sig
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
                                                                                [
                                                                                  {
                                                                                    [
                                                                                      Bool_match
                                                                                      [
                                                                                        [
                                                                                          [
                                                                                            verifySignature
                                                                                            w
                                                                                          ]
                                                                                          ww
                                                                                        ]
                                                                                        sig
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
                                                                                          [
                                                                                            trace
                                                                                            [
                                                                                              toPlutusString
                                                                                              [
                                                                                                [
                                                                                                  {
                                                                                                    Cons
                                                                                                    (con integer)
                                                                                                  }
                                                                                                  (con
                                                                                                    109
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
                                                                                                          99
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
                                                                                                                      112
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
                                                                                                                          98
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
                                                                                                                              107
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
                                                                                                                                  121
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
                                                                                                                                      119
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
                                                                                                                                                    118
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
                                                                                                                                                        108
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
                                                                                                                                                            100
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
                                                                                        (fun Unit Bool)
                                                                                      }
                                                                                      (lam
                                                                                        thunk
                                                                                        Unit
                                                                                        [
                                                                                          go
                                                                                          r
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
                                                                        (lam
                                                                          thunk
                                                                          Unit
                                                                          [
                                                                            go r
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
                                                [ go ww ]
                                              )
                                            )
                                          )
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
                                              (tyvardecl PendingTxIn (type))
                                              
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
                                                (datatypebind
                                                  (datatype
                                                    (tyvardecl PendingTx (type))
                                                    
                                                    PendingTx_match
                                                    (vardecl
                                                      PendingTx
                                                      (fun [List PendingTxIn] (fun [List PendingTxOut] (fun (con integer) (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun PendingTxIn (fun [Interval (con integer)] (fun [List [[Tuple2 (con bytestring)] (con bytestring)]] (fun (con bytestring) PendingTx))))))))
                                                    )
                                                  )
                                                )
                                                (let
                                                  (nonrec)
                                                  (termbind
                                                    (strict)
                                                    (vardecl
                                                      wvalidate
                                                      (fun [List (con bytestring)] (fun (con integer) (fun Unit (fun Unit (fun PendingTx Bool)))))
                                                    )
                                                    (lam
                                                      ww
                                                      [List (con bytestring)]
                                                      (lam
                                                        ww
                                                        (con integer)
                                                        (lam
                                                          w
                                                          Unit
                                                          (lam
                                                            w
                                                            Unit
                                                            (lam
                                                              w
                                                              PendingTx
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
                                                                                    PendingTx_match
                                                                                    w
                                                                                  ]
                                                                                  [List (con bytestring)]
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
                                                                                                      {
                                                                                                        [
                                                                                                          Bool_match
                                                                                                          [
                                                                                                            [
                                                                                                              [
                                                                                                                wtxSignedBy
                                                                                                                ww
                                                                                                              ]
                                                                                                              ww
                                                                                                            ]
                                                                                                            e
                                                                                                          ]
                                                                                                        ]
                                                                                                        (fun Unit [List (con bytestring)])
                                                                                                      }
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
                                                          MultiSig (type)
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
                                                          (fun MultiSig (fun Unit (fun Unit (fun PendingTx Bool))))
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
                                                                PendingTx
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
                                                                                    [
                                                                                      [
                                                                                        [
                                                                                          [
                                                                                            wvalidate
                                                                                            ww
                                                                                          ]
                                                                                          ww
                                                                                        ]
                                                                                        Unit
                                                                                      ]
                                                                                      Unit
                                                                                    ]
                                                                                    w
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