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
                        (tyvardecl These (fun (type) (fun (type) (type))))
                        (tyvardecl a (type)) (tyvardecl b (type))
                        These_match
                        (vardecl That (fun b [[These a] b]))
                        (vardecl These (fun a (fun b [[These a] b])))
                        (vardecl This (fun a [[These a] b]))
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
                                              [ { Nil_match a } l ] (fun Unit b)
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
                                                      [ { { foldr a } b } f ]
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
                                                            { Tuple2_match k } r
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
                                                                { Tuple2 k }
                                                                [[These v] r]
                                                              }
                                                              c
                                                            ]
                                                            [
                                                              { { That v } r } b
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
                                                        { foldr [[Tuple2 k] r] }
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
                                                              (strict)
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
                                                        { { Tuple2_match k } v }
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
                                                              { Tuple2 k }
                                                              [[These v] r]
                                                            }
                                                            c
                                                          ]
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
                                                            [ go ds ]
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
                                                                          (rec)
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
                                                                            go b
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
                                          [ go [ [ unionVal ls ] rs ] ]
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
                                          (tyvardecl
                                            UpperBound (fun (type) (type))
                                          )
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
                                                [
                                                  [
                                                    (builtin equalsInteger) arg
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
                                                      [ { b Bool } True ] False
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
                                            (nonrec)
                                            (termbind
                                              (strict)
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
                                                                                        ww
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
                                                                                              ww
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
                                                                          ww
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
                                              (rec)
                                              (datatypebind
                                                (datatype
                                                  (tyvardecl Data (type))
                                                  
                                                  Data_match
                                                  (vardecl
                                                    B
                                                    (fun (con bytestring) Data)
                                                  )
                                                  (vardecl
                                                    Constr
                                                    (fun (con integer) (fun [List Data] Data))
                                                  )
                                                  (vardecl
                                                    I (fun (con integer) Data)
                                                  )
                                                  (vardecl
                                                    List (fun [List Data] Data)
                                                  )
                                                  (vardecl
                                                    Map
                                                    (fun [List [[Tuple2 Data] Data]] Data)
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
                                                      PubKeyTxOut
                                                      (fun (con bytestring) PendingTxOutType)
                                                    )
                                                    (vardecl
                                                      ScriptTxOut
                                                      (fun (con bytestring) (fun Data PendingTxOutType))
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
                                                        (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun PendingTxOutType PendingTxOut))
                                                      )
                                                    )
                                                  )
                                                  (let
                                                    (nonrec)
                                                    (termbind
                                                      (strict)
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
                                                                      (nonrec)
                                                                      (termbind
                                                                        (strict)
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
                                                                            PendingTxOutType
                                                                            [
                                                                              [
                                                                                {
                                                                                  [
                                                                                    PendingTxOutType_match
                                                                                    ds
                                                                                  ]
                                                                                  [List PendingTxOut]
                                                                                }
                                                                                (lam
                                                                                  ipv
                                                                                  (con bytestring)
                                                                                  xs
                                                                                )
                                                                              ]
                                                                              (lam
                                                                                outHsh
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
                                                                    )
                                                                  )
                                                                )
                                                              ]
                                                              {
                                                                Nil PendingTxOut
                                                              }
                                                            ]
                                                            ww
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
                                                          (fun (con bytestring) (fun [List PendingTxOut] [List [[Tuple2 Data] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]]))
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
                                                                    [List [[Tuple2 Data] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]]
                                                                  }
                                                                  (lam
                                                                    e
                                                                    PendingTxOut
                                                                    (lam
                                                                      xs
                                                                      [List [[Tuple2 Data] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]]
                                                                      [
                                                                        {
                                                                          [
                                                                            PendingTxOut_match
                                                                            e
                                                                          ]
                                                                          [List [[Tuple2 Data] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]]
                                                                        }
                                                                        (lam
                                                                          ds
                                                                          [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                          (lam
                                                                            ds
                                                                            PendingTxOutType
                                                                            [
                                                                              [
                                                                                {
                                                                                  [
                                                                                    PendingTxOutType_match
                                                                                    ds
                                                                                  ]
                                                                                  [List [[Tuple2 Data] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]]
                                                                                }
                                                                                (lam
                                                                                  ipv
                                                                                  (con bytestring)
                                                                                  xs
                                                                                )
                                                                              ]
                                                                              (lam
                                                                                h
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
                                                                                                equalsByteString
                                                                                                w
                                                                                              ]
                                                                                              h
                                                                                            ]
                                                                                          ]
                                                                                          (fun Unit [List [[Tuple2 Data] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]])
                                                                                        }
                                                                                        (lam
                                                                                          thunk
                                                                                          Unit
                                                                                          [
                                                                                            [
                                                                                              {
                                                                                                Cons
                                                                                                [[Tuple2 Data] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                                                              }
                                                                                              [
                                                                                                [
                                                                                                  {
                                                                                                    {
                                                                                                      Tuple2
                                                                                                      Data
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
                                                                    )
                                                                  )
                                                                ]
                                                                {
                                                                  Nil
                                                                  [[Tuple2 Data] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
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
                                                                    (nonrec)
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
                                                                      (nonrec)
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
                                                                        (rec)
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
                                                                                    PendingTxOutType
                                                                                    ds
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
                                                                                  (fun VestingTranche (fun VestingTranche (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun [List PendingTxOut] (fun [PendingTxIn [[Tuple2 (con bytestring)] (con bytestring)]] (fun [Interval (con integer)] Bool))))))
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
                                                                                        ww
                                                                                        [List PendingTxOut]
                                                                                        (lam
                                                                                          ww
                                                                                          [PendingTxIn [[Tuple2 (con bytestring)] (con bytestring)]]
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
                                                                                                        addInteger
                                                                                                      ]
                                                                                                      [
                                                                                                        {
                                                                                                          [
                                                                                                            {
                                                                                                              PendingTxIn_match
                                                                                                              [[Tuple2 (con bytestring)] (con bytestring)]
                                                                                                            }
                                                                                                            ww
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
                                                                                                            ww
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
                                                                                                                            ww
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
                                                                                                                    [[Tuple2 Data] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                                                                                  }
                                                                                                                  [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                }
                                                                                                                {
                                                                                                                  {
                                                                                                                    snd
                                                                                                                    Data
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
                                                                                                                        ww
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
                                                                                                                ww
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
                                                                              (let
                                                                                (nonrec
                                                                                )
                                                                                (datatypebind
                                                                                  (datatype
                                                                                    (tyvardecl
                                                                                      Maybe
                                                                                      (fun (type) (type))
                                                                                    )
                                                                                    (tyvardecl
                                                                                      a
                                                                                      (type)
                                                                                    )
                                                                                    Maybe_match
                                                                                    (vardecl
                                                                                      Just
                                                                                      (fun a [Maybe a])
                                                                                    )
                                                                                    (vardecl
                                                                                      Nothing
                                                                                      [Maybe a]
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
                                                                                            (fun Vesting (fun VestingData (fun Unit (fun [PendingTx [PendingTxIn [[Tuple2 (con bytestring)] (con bytestring)]]] Bool))))
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
                                                                                                                    ww
                                                                                                                    [List [PendingTxIn [Maybe [[Tuple2 (con bytestring)] (con bytestring)]]]]
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
                                                                                                                            [PendingTxIn [[Tuple2 (con bytestring)] (con bytestring)]]
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