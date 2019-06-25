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
          (datatype
            (tyvardecl Bool (type))
            
            Bool_match
            (vardecl True Bool) (vardecl False Bool)
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
                                ds1
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
                                          { fFunctorNil_cfmap [[Tuple2 k] r] }
                                          [[Tuple2 k] [[These v] r]]
                                        }
                                        (lam
                                          ds2
                                          [[Tuple2 k] r]
                                          [
                                            {
                                              [ { { Tuple2_match k } r } ds2 ]
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
                                                      { Tuple2 k } [[These v] r]
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
                                                (let
                                                  (nonrec)
                                                  (termbind
                                                    (strict)
                                                    (vardecl wild [[Tuple2 k] r]
                                                    )
                                                    e
                                                  )
                                                  [
                                                    {
                                                      [
                                                        { { Tuple2_match k } r }
                                                        e
                                                      ]
                                                      [List [[Tuple2 k] r]]
                                                    }
                                                    (lam
                                                      c
                                                      k
                                                      (lam
                                                        ds2
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
                                                                          a1
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
                                                                                        a1
                                                                                      ]
                                                                                      Bool
                                                                                    }
                                                                                    (lam
                                                                                      c
                                                                                      k
                                                                                      (lam
                                                                                        ds3
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
                                                              (lam thunk Unit xs
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
                                        ds1
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
                                        ds2
                                        [[Tuple2 k] v]
                                        [
                                          {
                                            [ { { Tuple2_match k } v } ds2 ]
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
                                                  { { Tuple2 k } [[These v] r] }
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
                                                      ds3
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
                                                                ds3
                                                              ]
                                                              (fun Unit [[These v] r])
                                                            }
                                                            (lam
                                                              thunk
                                                              Unit
                                                              [
                                                                { { This v } r }
                                                                i
                                                              ]
                                                            )
                                                          ]
                                                          (lam
                                                            ds4
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
                                                                      ds4
                                                                    ]
                                                                    [[These v] r]
                                                                  }
                                                                  (lam
                                                                    c
                                                                    k
                                                                    (lam
                                                                      i1
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
                                                                                i1
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
                                                  [ go ds1 ]
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
                    (rec)
                    (termbind
                      (strict)
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
                                          [ [ { { map a } b } f ] xs ]
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
                          fst
                          (all a (type) (all b (type) (fun [[Tuple2 a] b] a)))
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
                                { [ { { Tuple2_match a } b } ds ] a }
                                (lam a1 a (lam ds1 b a1))
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
                              charToString (fun (con integer) (con string))
                            )
                            (builtin charToString)
                          )
                          (let
                            (nonrec)
                            (termbind
                              (strict) (vardecl emptyString (con string)) (con )
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
                                              [
                                                appendString [ charToString c ]
                                              ]
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
                                              [ (builtin equalsInteger) arg ]
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
                                          error (all a (type) (fun Unit a))
                                        )
                                        (abs e (type) (lam thunk Unit (error e))
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
                                              sha2_256
                                              (fun (con bytestring) (con bytestring))
                                            )
                                            (builtin sha2_256)
                                          )
                                          (let
                                            (nonrec)
                                            (termbind
                                              (strict)
                                              (vardecl
                                                trace (fun (con string) Unit)
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
                                                (nonstrict)
                                                (vardecl
                                                  swmkValidator3
                                                  [List (con integer)]
                                                )
                                                [
                                                  [
                                                    { Cons (con integer) }
                                                    (con 83)
                                                  ]
                                                  [
                                                    [
                                                      { Cons (con integer) }
                                                      (con 116)
                                                    ]
                                                    [
                                                      [
                                                        { Cons (con integer) }
                                                        (con 97)
                                                      ]
                                                      [
                                                        [
                                                          { Cons (con integer) }
                                                          (con 116)
                                                        ]
                                                        [
                                                          [
                                                            {
                                                              Cons (con integer)
                                                            }
                                                            (con 101)
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
                                                                (con 116)
                                                              ]
                                                              [
                                                                [
                                                                  {
                                                                    Cons
                                                                    (con integer)
                                                                  }
                                                                  (con 114)
                                                                ]
                                                                [
                                                                  [
                                                                    {
                                                                      Cons
                                                                      (con integer)
                                                                    }
                                                                    (con 97)
                                                                  ]
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
                                                                        (con 115
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
                                                                                                        45
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
                                                                                                                                                        113
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
                                                                                                                                                                                                104
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
                                              )
                                              (let
                                                (nonrec)
                                                (termbind
                                                  (nonstrict)
                                                  (vardecl
                                                    swmkValidator2 (con string)
                                                  )
                                                  [
                                                    toPlutusString
                                                    swmkValidator3
                                                  ]
                                                )
                                                (let
                                                  (nonrec)
                                                  (termbind
                                                    (nonstrict)
                                                    (vardecl swmkValidator1 Unit
                                                    )
                                                    [ trace swmkValidator2 ]
                                                  )
                                                  (let
                                                    (nonrec)
                                                    (termbind
                                                      (nonstrict)
                                                      (vardecl
                                                        swmkValidator4
                                                        [[Tuple2 (con bytestring)] (con bytestring)]
                                                      )
                                                      [
                                                        {
                                                          error
                                                          [[Tuple2 (con bytestring)] (con bytestring)]
                                                        }
                                                        Unit
                                                      ]
                                                    )
                                                    (let
                                                      (nonrec)
                                                      (termbind
                                                        (nonstrict)
                                                        (vardecl
                                                          swmkValidator7
                                                          [List (con integer)]
                                                        )
                                                        [
                                                          [
                                                            {
                                                              Cons (con integer)
                                                            }
                                                            (con 83)
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
                                                                (con 97)
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
                                                                    (con 101)
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
                                                                        (con 116
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
                                                                                                                45
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
                                                                                                                    39
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
                                                                                                                        120
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
                                                                                                                                      83
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
                                                                                                                                                39
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
                                                                                                                                                              113
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
                                                                                                                                                                              39
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
                                                                                                                                                                                      83
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
                                                                                                                                                                                                39
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
                                                      )
                                                      (let
                                                        (nonrec)
                                                        (termbind
                                                          (nonstrict)
                                                          (vardecl
                                                            swmkValidator6
                                                            (con string)
                                                          )
                                                          [
                                                            toPlutusString
                                                            swmkValidator7
                                                          ]
                                                        )
                                                        (let
                                                          (nonrec)
                                                          (termbind
                                                            (nonstrict)
                                                            (vardecl
                                                              swmkValidator5
                                                              Unit
                                                            )
                                                            [
                                                              trace
                                                              swmkValidator6
                                                            ]
                                                          )
                                                          (let
                                                            (nonrec)
                                                            (datatypebind
                                                              (datatype
                                                                (tyvardecl
                                                                  GameState
                                                                  (type)
                                                                )
                                                                
                                                                GameState_match
                                                                (vardecl
                                                                  Initialised
                                                                  (fun (con bytestring) GameState)
                                                                )
                                                                (vardecl
                                                                  Locked
                                                                  (fun (con bytestring) (fun (con bytestring) GameState))
                                                                )
                                                              )
                                                            )
                                                            (let
                                                              (nonrec)
                                                              (termbind
                                                                (strict)
                                                                (vardecl
                                                                  fEqGameState_c
                                                                  (fun GameState (fun GameState Bool))
                                                                )
                                                                (lam
                                                                  ds
                                                                  GameState
                                                                  (lam
                                                                    ds1
                                                                    GameState
                                                                    (let
                                                                      (nonrec)
                                                                      (termbind
                                                                        (strict)
                                                                        (vardecl
                                                                          fail
                                                                          (fun (all a (type) (fun Unit a)) Bool)
                                                                        )
                                                                        (lam
                                                                          ds2
                                                                          (all a (type) (fun Unit a))
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
                                                                                                                    113
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
                                                                      )
                                                                      [
                                                                        [
                                                                          {
                                                                            [
                                                                              GameState_match
                                                                              ds
                                                                            ]
                                                                            Bool
                                                                          }
                                                                          (lam
                                                                            ds2
                                                                            (con bytestring)
                                                                            [
                                                                              [
                                                                                {
                                                                                  [
                                                                                    GameState_match
                                                                                    ds1
                                                                                  ]
                                                                                  Bool
                                                                                }
                                                                                (lam
                                                                                  ds3
                                                                                  (con bytestring)
                                                                                  [
                                                                                    [
                                                                                      equalsByteString
                                                                                      ds2
                                                                                    ]
                                                                                    ds3
                                                                                  ]
                                                                                )
                                                                              ]
                                                                              (lam
                                                                                ipv
                                                                                (con bytestring)
                                                                                (lam
                                                                                  ipv1
                                                                                  (con bytestring)
                                                                                  [
                                                                                    fail
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
                                                                                  ]
                                                                                )
                                                                              )
                                                                            ]
                                                                          )
                                                                        ]
                                                                        (lam
                                                                          ds2
                                                                          (con bytestring)
                                                                          (lam
                                                                            ds3
                                                                            (con bytestring)
                                                                            [
                                                                              [
                                                                                {
                                                                                  [
                                                                                    GameState_match
                                                                                    ds1
                                                                                  ]
                                                                                  Bool
                                                                                }
                                                                                (lam
                                                                                  ipv
                                                                                  (con bytestring)
                                                                                  [
                                                                                    fail
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
                                                                                  ]
                                                                                )
                                                                              ]
                                                                              (lam
                                                                                ds4
                                                                                (con bytestring)
                                                                                (lam
                                                                                  ds5
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
                                                                                                ds3
                                                                                              ]
                                                                                              ds5
                                                                                            ]
                                                                                          ]
                                                                                          (fun Unit Bool)
                                                                                        }
                                                                                        (lam
                                                                                          thunk
                                                                                          Unit
                                                                                          [
                                                                                            [
                                                                                              equalsByteString
                                                                                              ds2
                                                                                            ]
                                                                                            ds4
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
                                                                      Maybe
                                                                      (fun (type) (type))
                                                                    )
                                                                    (tyvardecl
                                                                      a (type)
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
                                                                        (fun [Maybe a] (fun [Maybe a] [Interval a]))
                                                                      )
                                                                    )
                                                                  )
                                                                  (let
                                                                    (nonrec)
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
                                                                      (nonrec)
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
                                                                        (nonrec)
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
                                                                                              ds1
                                                                                              [Maybe [[Tuple2 (con bytestring)] (con bytestring)]]
                                                                                              (lam
                                                                                                ds2
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
                                                                                                          ds1
                                                                                                        ]
                                                                                                        (fun Unit [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]])
                                                                                                      }
                                                                                                      (lam
                                                                                                        ds3
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
                                                                                                                ds3
                                                                                                              ]
                                                                                                              [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]]
                                                                                                            }
                                                                                                            (lam
                                                                                                              h
                                                                                                              (con bytestring)
                                                                                                              (lam
                                                                                                                ds4
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
                                                                                                                                ds4
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
                                                                                (termbind
                                                                                  (strict
                                                                                  )
                                                                                  (vardecl
                                                                                    swmkValidator
                                                                                    (all i (type) (fun [[(lam s (type) (lam i (type) (fun s (fun i s)))) GameState] i] (fun GameState (fun GameState (fun [Maybe i] (fun PendingTx Bool))))))
                                                                                  )
                                                                                  (abs
                                                                                    i
                                                                                    (type)
                                                                                    (lam
                                                                                      w5
                                                                                      [[(lam s (type) (lam i (type) (fun s (fun i s)))) GameState] i]
                                                                                      (lam
                                                                                        ww
                                                                                        GameState
                                                                                        (lam
                                                                                          ww1
                                                                                          GameState
                                                                                          (lam
                                                                                            ww2
                                                                                            [Maybe i]
                                                                                            (lam
                                                                                              w6
                                                                                              PendingTx
                                                                                              [
                                                                                                [
                                                                                                  [
                                                                                                    {
                                                                                                      [
                                                                                                        {
                                                                                                          Maybe_match
                                                                                                          i
                                                                                                        }
                                                                                                        ww2
                                                                                                      ]
                                                                                                      (fun Unit Bool)
                                                                                                    }
                                                                                                    (lam
                                                                                                      input
                                                                                                      i
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
                                                                                                                      fEqGameState_c
                                                                                                                      [
                                                                                                                        [
                                                                                                                          w5
                                                                                                                          ww
                                                                                                                        ]
                                                                                                                        input
                                                                                                                      ]
                                                                                                                    ]
                                                                                                                    ww1
                                                                                                                  ]
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
                                                                                                                      w6
                                                                                                                    ]
                                                                                                                    Bool
                                                                                                                  }
                                                                                                                  (lam
                                                                                                                    ww4
                                                                                                                    [List PendingTxIn]
                                                                                                                    (lam
                                                                                                                      ww5
                                                                                                                      [List PendingTxOut]
                                                                                                                      (lam
                                                                                                                        ww6
                                                                                                                        (con integer)
                                                                                                                        (lam
                                                                                                                          ww7
                                                                                                                          [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                          (lam
                                                                                                                            ww8
                                                                                                                            PendingTxIn
                                                                                                                            (lam
                                                                                                                              ww9
                                                                                                                              [Interval (con integer)]
                                                                                                                              (lam
                                                                                                                                ww10
                                                                                                                                [List [[Tuple2 (con bytestring)] (con bytestring)]]
                                                                                                                                (lam
                                                                                                                                  ww11
                                                                                                                                  (con bytestring)
                                                                                                                                  (let
                                                                                                                                    (nonrec
                                                                                                                                    )
                                                                                                                                    (termbind
                                                                                                                                      (nonstrict
                                                                                                                                      )
                                                                                                                                      (vardecl
                                                                                                                                        rh
                                                                                                                                        (con bytestring)
                                                                                                                                      )
                                                                                                                                      [
                                                                                                                                        {
                                                                                                                                          [
                                                                                                                                            PendingTxIn_match
                                                                                                                                            ww8
                                                                                                                                          ]
                                                                                                                                          (con bytestring)
                                                                                                                                        }
                                                                                                                                        (lam
                                                                                                                                          ds8
                                                                                                                                          PendingTxOutRef
                                                                                                                                          (lam
                                                                                                                                            ds9
                                                                                                                                            [Maybe [[Tuple2 (con bytestring)] (con bytestring)]]
                                                                                                                                            (lam
                                                                                                                                              ds10
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
                                                                                                                                                        ds9
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
                                                                                                                                                            vh
                                                                                                                                                            (con bytestring)
                                                                                                                                                            (lam
                                                                                                                                                              ds11
                                                                                                                                                              (con bytestring)
                                                                                                                                                              ds11
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
                                                                                                                                                          swmkValidator4
                                                                                                                                                        ]
                                                                                                                                                        (con bytestring)
                                                                                                                                                      }
                                                                                                                                                      (lam
                                                                                                                                                        vh
                                                                                                                                                        (con bytestring)
                                                                                                                                                        (lam
                                                                                                                                                          ds11
                                                                                                                                                          (con bytestring)
                                                                                                                                                          ds11
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
                                                                                                                                                        (con bytestring)
                                                                                                                                                      }
                                                                                                                                                      Bool
                                                                                                                                                    }
                                                                                                                                                    (lam
                                                                                                                                                      a1
                                                                                                                                                      (con bytestring)
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
                                                                                                                                                                [
                                                                                                                                                                  [
                                                                                                                                                                    equalsByteString
                                                                                                                                                                    a1
                                                                                                                                                                  ]
                                                                                                                                                                  rh
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
                                                                                                                                                  True
                                                                                                                                                ]
                                                                                                                                                [
                                                                                                                                                  [
                                                                                                                                                    {
                                                                                                                                                      {
                                                                                                                                                        fFunctorNil_cfmap
                                                                                                                                                        [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                                                                                                                      }
                                                                                                                                                      (con bytestring)
                                                                                                                                                    }
                                                                                                                                                    {
                                                                                                                                                      {
                                                                                                                                                        fst
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
                                                                                                                                                            ww8
                                                                                                                                                          ]
                                                                                                                                                          (con bytestring)
                                                                                                                                                        }
                                                                                                                                                        (lam
                                                                                                                                                          ds8
                                                                                                                                                          PendingTxOutRef
                                                                                                                                                          (lam
                                                                                                                                                            ds9
                                                                                                                                                            [Maybe [[Tuple2 (con bytestring)] (con bytestring)]]
                                                                                                                                                            (lam
                                                                                                                                                              ds10
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
                                                                                                                                                                        ds9
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
                                                                                                                                                                            vh
                                                                                                                                                                            (con bytestring)
                                                                                                                                                                            (lam
                                                                                                                                                                              ds11
                                                                                                                                                                              (con bytestring)
                                                                                                                                                                              vh
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
                                                                                                                                                                          swmkValidator4
                                                                                                                                                                        ]
                                                                                                                                                                        (con bytestring)
                                                                                                                                                                      }
                                                                                                                                                                      (lam
                                                                                                                                                                        vh
                                                                                                                                                                        (con bytestring)
                                                                                                                                                                        (lam
                                                                                                                                                                          ds11
                                                                                                                                                                          (con bytestring)
                                                                                                                                                                          vh
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
                                                                                                                                                    ww5
                                                                                                                                                  ]
                                                                                                                                                ]
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
                                                                                                                                                  swmkValidator1
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
                                                                                                                          )
                                                                                                                        )
                                                                                                                      )
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
                                                                                                                  {
                                                                                                                    [
                                                                                                                      Unit_match
                                                                                                                      swmkValidator5
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
                                                                                (let
                                                                                  (nonrec
                                                                                  )
                                                                                  (datatypebind
                                                                                    (datatype
                                                                                      (tyvardecl
                                                                                        GameInput
                                                                                        (type)
                                                                                      )
                                                                                      
                                                                                      GameInput_match
                                                                                      (vardecl
                                                                                        ForgeToken
                                                                                        (fun (con bytestring) GameInput)
                                                                                      )
                                                                                      (vardecl
                                                                                        Guess
                                                                                        (fun (con bytestring) (fun (con bytestring) GameInput))
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
                                                                                        gameTokenVal5
                                                                                        (con integer)
                                                                                      )
                                                                                      (con
                                                                                        1
                                                                                      )
                                                                                    )
                                                                                    (let
                                                                                      (nonrec
                                                                                      )
                                                                                      (termbind
                                                                                        (nonstrict
                                                                                        )
                                                                                        (vardecl
                                                                                          mkValidator4
                                                                                          [List (con integer)]
                                                                                        )
                                                                                        [
                                                                                          [
                                                                                            {
                                                                                              Cons
                                                                                              (con integer)
                                                                                            }
                                                                                            (con
                                                                                              73
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
                                                                                                              83
                                                                                                            )
                                                                                                          ]
                                                                                                          [
                                                                                                            [
                                                                                                              {
                                                                                                                Cons
                                                                                                                (con integer)
                                                                                                              }
                                                                                                              (con
                                                                                                                77
                                                                                                              )
                                                                                                            ]
                                                                                                            [
                                                                                                              [
                                                                                                                {
                                                                                                                  Cons
                                                                                                                  (con integer)
                                                                                                                }
                                                                                                                (con
                                                                                                                  46
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
                                                                                                                                      110
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
                                                                                        (nonrec
                                                                                        )
                                                                                        (termbind
                                                                                          (nonstrict
                                                                                          )
                                                                                          (vardecl
                                                                                            mkValidator3
                                                                                            (con string)
                                                                                          )
                                                                                          [
                                                                                            toPlutusString
                                                                                            mkValidator4
                                                                                          ]
                                                                                        )
                                                                                        (let
                                                                                          (nonrec
                                                                                          )
                                                                                          (termbind
                                                                                            (nonstrict
                                                                                            )
                                                                                            (vardecl
                                                                                              mkValidator2
                                                                                              Unit
                                                                                            )
                                                                                            [
                                                                                              trace
                                                                                              mkValidator3
                                                                                            ]
                                                                                          )
                                                                                          (let
                                                                                            (nonrec
                                                                                            )
                                                                                            (termbind
                                                                                              (nonstrict
                                                                                              )
                                                                                              (vardecl
                                                                                                mkValidator1
                                                                                                GameState
                                                                                              )
                                                                                              [
                                                                                                {
                                                                                                  error
                                                                                                  GameState
                                                                                                }
                                                                                                mkValidator2
                                                                                              ]
                                                                                            )
                                                                                            (let
                                                                                              (nonrec
                                                                                              )
                                                                                              (termbind
                                                                                                (nonstrict
                                                                                                )
                                                                                                (vardecl
                                                                                                  mkValidator5
                                                                                                  GameState
                                                                                                )
                                                                                                [
                                                                                                  {
                                                                                                    error
                                                                                                    GameState
                                                                                                  }
                                                                                                  Unit
                                                                                                ]
                                                                                              )
                                                                                              (let
                                                                                                (nonrec
                                                                                                )
                                                                                                (termbind
                                                                                                  (strict
                                                                                                  )
                                                                                                  (vardecl
                                                                                                    pendingTxForge
                                                                                                    (fun PendingTx [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]])
                                                                                                  )
                                                                                                  (lam
                                                                                                    ds
                                                                                                    PendingTx
                                                                                                    [
                                                                                                      {
                                                                                                        [
                                                                                                          PendingTx_match
                                                                                                          ds
                                                                                                        ]
                                                                                                        [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                      }
                                                                                                      (lam
                                                                                                        ds1
                                                                                                        [List PendingTxIn]
                                                                                                        (lam
                                                                                                          ds2
                                                                                                          [List PendingTxOut]
                                                                                                          (lam
                                                                                                            ds3
                                                                                                            (con integer)
                                                                                                            (lam
                                                                                                              ds4
                                                                                                              [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                              (lam
                                                                                                                ds5
                                                                                                                PendingTxIn
                                                                                                                (lam
                                                                                                                  ds6
                                                                                                                  [Interval (con integer)]
                                                                                                                  (lam
                                                                                                                    ds7
                                                                                                                    [List [[Tuple2 (con bytestring)] (con bytestring)]]
                                                                                                                    (lam
                                                                                                                      ds8
                                                                                                                      (con bytestring)
                                                                                                                      ds4
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
                                                                                                  (nonrec
                                                                                                  )
                                                                                                  (termbind
                                                                                                    (strict
                                                                                                    )
                                                                                                    (vardecl
                                                                                                      pendingTxInValue
                                                                                                      (fun PendingTxIn [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]])
                                                                                                    )
                                                                                                    (lam
                                                                                                      ds
                                                                                                      PendingTxIn
                                                                                                      [
                                                                                                        {
                                                                                                          [
                                                                                                            PendingTxIn_match
                                                                                                            ds
                                                                                                          ]
                                                                                                          [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                        }
                                                                                                        (lam
                                                                                                          ds1
                                                                                                          PendingTxOutRef
                                                                                                          (lam
                                                                                                            ds2
                                                                                                            [Maybe [[Tuple2 (con bytestring)] (con bytestring)]]
                                                                                                            (lam
                                                                                                              ds3
                                                                                                              [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                              ds3
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
                                                                                                        unionVal
                                                                                                        (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]]))
                                                                                                      )
                                                                                                      (lam
                                                                                                        ds
                                                                                                        [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                        (lam
                                                                                                          ds1
                                                                                                          [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                          (let
                                                                                                            (rec
                                                                                                            )
                                                                                                            (termbind
                                                                                                              (strict
                                                                                                              )
                                                                                                              (vardecl
                                                                                                                go7
                                                                                                                (fun [List [[Tuple2 (con bytestring)] [[These [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]] [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]]])
                                                                                                              )
                                                                                                              (lam
                                                                                                                ds2
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
                                                                                                                          ds2
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
                                                                                                                      ds3
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
                                                                                                                                ds3
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
                                                                                                                                                    go8
                                                                                                                                                    (fun [List [[Tuple2 (con bytestring)] (con integer)]] [List [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]])
                                                                                                                                                  )
                                                                                                                                                  (lam
                                                                                                                                                    ds4
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
                                                                                                                                                              ds4
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
                                                                                                                                                          ds5
                                                                                                                                                          [[Tuple2 (con bytestring)] (con integer)]
                                                                                                                                                          (lam
                                                                                                                                                            xs1
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
                                                                                                                                                                    ds5
                                                                                                                                                                  ]
                                                                                                                                                                  [List [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]]
                                                                                                                                                                }
                                                                                                                                                                (lam
                                                                                                                                                                  c1
                                                                                                                                                                  (con bytestring)
                                                                                                                                                                  (lam
                                                                                                                                                                    i1
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
                                                                                                                                                                            c1
                                                                                                                                                                          ]
                                                                                                                                                                          [
                                                                                                                                                                            {
                                                                                                                                                                              {
                                                                                                                                                                                That
                                                                                                                                                                                (con integer)
                                                                                                                                                                              }
                                                                                                                                                                              (con integer)
                                                                                                                                                                            }
                                                                                                                                                                            i1
                                                                                                                                                                          ]
                                                                                                                                                                        ]
                                                                                                                                                                      ]
                                                                                                                                                                      [
                                                                                                                                                                        go8
                                                                                                                                                                        xs1
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
                                                                                                                                                  go8
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
                                                                                                                                                go8
                                                                                                                                                (fun [List [[Tuple2 (con bytestring)] (con integer)]] [List [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]])
                                                                                                                                              )
                                                                                                                                              (lam
                                                                                                                                                ds4
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
                                                                                                                                                          ds4
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
                                                                                                                                                      ds5
                                                                                                                                                      [[Tuple2 (con bytestring)] (con integer)]
                                                                                                                                                      (lam
                                                                                                                                                        xs1
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
                                                                                                                                                                ds5
                                                                                                                                                              ]
                                                                                                                                                              [List [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]]
                                                                                                                                                            }
                                                                                                                                                            (lam
                                                                                                                                                              c1
                                                                                                                                                              (con bytestring)
                                                                                                                                                              (lam
                                                                                                                                                                i1
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
                                                                                                                                                                        c1
                                                                                                                                                                      ]
                                                                                                                                                                      [
                                                                                                                                                                        {
                                                                                                                                                                          {
                                                                                                                                                                            This
                                                                                                                                                                            (con integer)
                                                                                                                                                                          }
                                                                                                                                                                          (con integer)
                                                                                                                                                                        }
                                                                                                                                                                        i1
                                                                                                                                                                      ]
                                                                                                                                                                    ]
                                                                                                                                                                  ]
                                                                                                                                                                  [
                                                                                                                                                                    go8
                                                                                                                                                                    xs1
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
                                                                                                                                              go8
                                                                                                                                              a
                                                                                                                                            ]
                                                                                                                                          )
                                                                                                                                        )
                                                                                                                                      ]
                                                                                                                                    ]
                                                                                                                                  ]
                                                                                                                                  [
                                                                                                                                    go7
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
                                                                                                              go7
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
                                                                                                                ds1
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
                                                                                                                    go7
                                                                                                                    (fun [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]]] [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]])
                                                                                                                  )
                                                                                                                  (lam
                                                                                                                    ds1
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
                                                                                                                              ds1
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
                                                                                                                          ds2
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
                                                                                                                                    ds2
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
                                                                                                                                                go8
                                                                                                                                                (fun [List [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]] [List [[Tuple2 (con bytestring)] (con integer)]])
                                                                                                                                              )
                                                                                                                                              (lam
                                                                                                                                                ds4
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
                                                                                                                                                          ds4
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
                                                                                                                                                      ds5
                                                                                                                                                      [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]
                                                                                                                                                      (lam
                                                                                                                                                        xs1
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
                                                                                                                                                                ds5
                                                                                                                                                              ]
                                                                                                                                                              [List [[Tuple2 (con bytestring)] (con integer)]]
                                                                                                                                                            }
                                                                                                                                                            (lam
                                                                                                                                                              c1
                                                                                                                                                              (con bytestring)
                                                                                                                                                              (lam
                                                                                                                                                                i1
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
                                                                                                                                                                        c1
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
                                                                                                                                                                                i1
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
                                                                                                                                                                    go8
                                                                                                                                                                    xs1
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
                                                                                                                                              go8
                                                                                                                                              i
                                                                                                                                            ]
                                                                                                                                          )
                                                                                                                                        ]
                                                                                                                                      ]
                                                                                                                                      [
                                                                                                                                        go7
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
                                                                                                                  go7
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
                                                                                                          (strict
                                                                                                          )
                                                                                                          (vardecl
                                                                                                            wvalueSpent
                                                                                                            (fun [List PendingTxIn] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]])
                                                                                                          )
                                                                                                          (lam
                                                                                                            ww
                                                                                                            [List PendingTxIn]
                                                                                                            (let
                                                                                                              (rec
                                                                                                              )
                                                                                                              (termbind
                                                                                                                (strict
                                                                                                                )
                                                                                                                (vardecl
                                                                                                                  go4
                                                                                                                  (fun [List [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]])
                                                                                                                )
                                                                                                                (lam
                                                                                                                  ds
                                                                                                                  [List [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                                                                                  [
                                                                                                                    [
                                                                                                                      [
                                                                                                                        {
                                                                                                                          [
                                                                                                                            {
                                                                                                                              Nil_match
                                                                                                                              [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                            }
                                                                                                                            ds
                                                                                                                          ]
                                                                                                                          (fun Unit [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]])
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
                                                                                                                        y
                                                                                                                        [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                        (lam
                                                                                                                          ys
                                                                                                                          [List [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                                                                                          (lam
                                                                                                                            thunk
                                                                                                                            Unit
                                                                                                                            [
                                                                                                                              [
                                                                                                                                [
                                                                                                                                  unionWith
                                                                                                                                  addInteger
                                                                                                                                ]
                                                                                                                                y
                                                                                                                              ]
                                                                                                                              [
                                                                                                                                go4
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
                                                                                                              [
                                                                                                                go4
                                                                                                                [
                                                                                                                  [
                                                                                                                    {
                                                                                                                      {
                                                                                                                        map
                                                                                                                        PendingTxIn
                                                                                                                      }
                                                                                                                      [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                    }
                                                                                                                    pendingTxInValue
                                                                                                                  ]
                                                                                                                  ww
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
                                                                                                              valueSpent
                                                                                                              (fun PendingTx [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]])
                                                                                                            )
                                                                                                            (lam
                                                                                                              w
                                                                                                              PendingTx
                                                                                                              [
                                                                                                                {
                                                                                                                  [
                                                                                                                    PendingTx_match
                                                                                                                    w
                                                                                                                  ]
                                                                                                                  [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                }
                                                                                                                (lam
                                                                                                                  ww1
                                                                                                                  [List PendingTxIn]
                                                                                                                  (lam
                                                                                                                    ww2
                                                                                                                    [List PendingTxOut]
                                                                                                                    (lam
                                                                                                                      ww3
                                                                                                                      (con integer)
                                                                                                                      (lam
                                                                                                                        ww4
                                                                                                                        [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                        (lam
                                                                                                                          ww5
                                                                                                                          PendingTxIn
                                                                                                                          (lam
                                                                                                                            ww6
                                                                                                                            [Interval (con integer)]
                                                                                                                            (lam
                                                                                                                              ww7
                                                                                                                              [List [[Tuple2 (con bytestring)] (con bytestring)]]
                                                                                                                              (lam
                                                                                                                                ww8
                                                                                                                                (con bytestring)
                                                                                                                                [
                                                                                                                                  wvalueSpent
                                                                                                                                  ww1
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
                                                                                                                          go7
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
                                                                                                                                ds1
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
                                                                                                                                          ds1
                                                                                                                                        ]
                                                                                                                                        Bool
                                                                                                                                      }
                                                                                                                                      (lam
                                                                                                                                        ds2
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
                                                                                                                                                go8
                                                                                                                                                (fun [List [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]] Bool)
                                                                                                                                              )
                                                                                                                                              (lam
                                                                                                                                                xs1
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
                                                                                                                                                          xs1
                                                                                                                                                        ]
                                                                                                                                                        (fun Unit Bool)
                                                                                                                                                      }
                                                                                                                                                      (lam
                                                                                                                                                        thunk
                                                                                                                                                        Unit
                                                                                                                                                        [
                                                                                                                                                          go7
                                                                                                                                                          xs
                                                                                                                                                        ]
                                                                                                                                                      )
                                                                                                                                                    ]
                                                                                                                                                    (lam
                                                                                                                                                      ds4
                                                                                                                                                      [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]
                                                                                                                                                      (lam
                                                                                                                                                        xs1
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
                                                                                                                                                                ds4
                                                                                                                                                              ]
                                                                                                                                                              Bool
                                                                                                                                                            }
                                                                                                                                                            (lam
                                                                                                                                                              ds5
                                                                                                                                                              (con bytestring)
                                                                                                                                                              (lam
                                                                                                                                                                x1
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
                                                                                                                                                                          x1
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
                                                                                                                                                                                  go8
                                                                                                                                                                                  xs1
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
                                                                                                                                                                                  go8
                                                                                                                                                                                  xs1
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
                                                                                                                                                                              go8
                                                                                                                                                                              xs1
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
                                                                                                                                              go8
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
                                                                                                                        go7
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
                                                                                                                  wmkValidator
                                                                                                                  (fun GameState (fun GameState (fun [Maybe GameInput] (fun PendingTx Bool))))
                                                                                                                )
                                                                                                                (lam
                                                                                                                  ww
                                                                                                                  GameState
                                                                                                                  (lam
                                                                                                                    ww1
                                                                                                                    GameState
                                                                                                                    (lam
                                                                                                                      ww2
                                                                                                                      [Maybe GameInput]
                                                                                                                      (lam
                                                                                                                        w
                                                                                                                        PendingTx
                                                                                                                        [
                                                                                                                          [
                                                                                                                            [
                                                                                                                              [
                                                                                                                                [
                                                                                                                                  {
                                                                                                                                    swmkValidator
                                                                                                                                    GameInput
                                                                                                                                  }
                                                                                                                                  (lam
                                                                                                                                    ds
                                                                                                                                    GameState
                                                                                                                                    (lam
                                                                                                                                      ds1
                                                                                                                                      GameInput
                                                                                                                                      [
                                                                                                                                        [
                                                                                                                                          {
                                                                                                                                            [
                                                                                                                                              GameState_match
                                                                                                                                              ds
                                                                                                                                            ]
                                                                                                                                            GameState
                                                                                                                                          }
                                                                                                                                          (lam
                                                                                                                                            s
                                                                                                                                            (con bytestring)
                                                                                                                                            [
                                                                                                                                              [
                                                                                                                                                {
                                                                                                                                                  [
                                                                                                                                                    GameInput_match
                                                                                                                                                    ds1
                                                                                                                                                  ]
                                                                                                                                                  GameState
                                                                                                                                                }
                                                                                                                                                (lam
                                                                                                                                                  tn
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
                                                                                                                                                                  checkBinRel
                                                                                                                                                                  equalsInteger
                                                                                                                                                                ]
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
                                                                                                                                                                        [
                                                                                                                                                                          {
                                                                                                                                                                            [
                                                                                                                                                                              PendingTx_match
                                                                                                                                                                              w
                                                                                                                                                                            ]
                                                                                                                                                                            (con bytestring)
                                                                                                                                                                          }
                                                                                                                                                                          (lam
                                                                                                                                                                            ww4
                                                                                                                                                                            [List PendingTxIn]
                                                                                                                                                                            (lam
                                                                                                                                                                              ww5
                                                                                                                                                                              [List PendingTxOut]
                                                                                                                                                                              (lam
                                                                                                                                                                                ww6
                                                                                                                                                                                (con integer)
                                                                                                                                                                                (lam
                                                                                                                                                                                  ww7
                                                                                                                                                                                  [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                                                                                  (lam
                                                                                                                                                                                    ww8
                                                                                                                                                                                    PendingTxIn
                                                                                                                                                                                    (lam
                                                                                                                                                                                      ww9
                                                                                                                                                                                      [Interval (con integer)]
                                                                                                                                                                                      (lam
                                                                                                                                                                                        ww10
                                                                                                                                                                                        [List [[Tuple2 (con bytestring)] (con bytestring)]]
                                                                                                                                                                                        (lam
                                                                                                                                                                                          ww11
                                                                                                                                                                                          (con bytestring)
                                                                                                                                                                                          [
                                                                                                                                                                                            {
                                                                                                                                                                                              [
                                                                                                                                                                                                PendingTxIn_match
                                                                                                                                                                                                ww8
                                                                                                                                                                                              ]
                                                                                                                                                                                              (con bytestring)
                                                                                                                                                                                            }
                                                                                                                                                                                            (lam
                                                                                                                                                                                              ww13
                                                                                                                                                                                              PendingTxOutRef
                                                                                                                                                                                              (lam
                                                                                                                                                                                                ww14
                                                                                                                                                                                                [Maybe [[Tuple2 (con bytestring)] (con bytestring)]]
                                                                                                                                                                                                (lam
                                                                                                                                                                                                  ww15
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
                                                                                                                                                                                                            ww14
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
                                                                                                                                                                                                                a1
                                                                                                                                                                                                                (con bytestring)
                                                                                                                                                                                                                (lam
                                                                                                                                                                                                                  ds2
                                                                                                                                                                                                                  (con bytestring)
                                                                                                                                                                                                                  a1
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
                                                                                                                                                                                                              swmkValidator4
                                                                                                                                                                                                            ]
                                                                                                                                                                                                            (con bytestring)
                                                                                                                                                                                                          }
                                                                                                                                                                                                          (lam
                                                                                                                                                                                                            a1
                                                                                                                                                                                                            (con bytestring)
                                                                                                                                                                                                            (lam
                                                                                                                                                                                                              ds2
                                                                                                                                                                                                              (con bytestring)
                                                                                                                                                                                                              a1
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
                                                                                                                                                                                      )
                                                                                                                                                                                    )
                                                                                                                                                                                  )
                                                                                                                                                                                )
                                                                                                                                                                              )
                                                                                                                                                                            )
                                                                                                                                                                          )
                                                                                                                                                                        ]
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
                                                                                                                                                                              tn
                                                                                                                                                                            ]
                                                                                                                                                                            gameTokenVal5
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
                                                                                                                                                              ]
                                                                                                                                                              [
                                                                                                                                                                pendingTxForge
                                                                                                                                                                w
                                                                                                                                                              ]
                                                                                                                                                            ]
                                                                                                                                                          ]
                                                                                                                                                          (fun Unit GameState)
                                                                                                                                                        }
                                                                                                                                                        (lam
                                                                                                                                                          thunk
                                                                                                                                                          Unit
                                                                                                                                                          [
                                                                                                                                                            [
                                                                                                                                                              Locked
                                                                                                                                                              tn
                                                                                                                                                            ]
                                                                                                                                                            s
                                                                                                                                                          ]
                                                                                                                                                        )
                                                                                                                                                      ]
                                                                                                                                                      (lam
                                                                                                                                                        thunk
                                                                                                                                                        Unit
                                                                                                                                                        mkValidator5
                                                                                                                                                      )
                                                                                                                                                    ]
                                                                                                                                                    Unit
                                                                                                                                                  ]
                                                                                                                                                )
                                                                                                                                              ]
                                                                                                                                              (lam
                                                                                                                                                ipv
                                                                                                                                                (con bytestring)
                                                                                                                                                (lam
                                                                                                                                                  ipv1
                                                                                                                                                  (con bytestring)
                                                                                                                                                  mkValidator1
                                                                                                                                                )
                                                                                                                                              )
                                                                                                                                            ]
                                                                                                                                          )
                                                                                                                                        ]
                                                                                                                                        (lam
                                                                                                                                          tn
                                                                                                                                          (con bytestring)
                                                                                                                                          (lam
                                                                                                                                            currentSecret
                                                                                                                                            (con bytestring)
                                                                                                                                            [
                                                                                                                                              [
                                                                                                                                                {
                                                                                                                                                  [
                                                                                                                                                    GameInput_match
                                                                                                                                                    ds1
                                                                                                                                                  ]
                                                                                                                                                  GameState
                                                                                                                                                }
                                                                                                                                                (lam
                                                                                                                                                  ipv
                                                                                                                                                  (con bytestring)
                                                                                                                                                  mkValidator1
                                                                                                                                                )
                                                                                                                                              ]
                                                                                                                                              (lam
                                                                                                                                                theGuess
                                                                                                                                                (con bytestring)
                                                                                                                                                (lam
                                                                                                                                                  nextSecret
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
                                                                                                                                                                currentSecret
                                                                                                                                                              ]
                                                                                                                                                              [
                                                                                                                                                                sha2_256
                                                                                                                                                                theGuess
                                                                                                                                                              ]
                                                                                                                                                            ]
                                                                                                                                                          ]
                                                                                                                                                          (fun Unit GameState)
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
                                                                                                                                                                          valueSpent
                                                                                                                                                                          w
                                                                                                                                                                        ]
                                                                                                                                                                      ]
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
                                                                                                                                                                              [
                                                                                                                                                                                {
                                                                                                                                                                                  [
                                                                                                                                                                                    PendingTx_match
                                                                                                                                                                                    w
                                                                                                                                                                                  ]
                                                                                                                                                                                  (con bytestring)
                                                                                                                                                                                }
                                                                                                                                                                                (lam
                                                                                                                                                                                  ww4
                                                                                                                                                                                  [List PendingTxIn]
                                                                                                                                                                                  (lam
                                                                                                                                                                                    ww5
                                                                                                                                                                                    [List PendingTxOut]
                                                                                                                                                                                    (lam
                                                                                                                                                                                      ww6
                                                                                                                                                                                      (con integer)
                                                                                                                                                                                      (lam
                                                                                                                                                                                        ww7
                                                                                                                                                                                        [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                                                                                        (lam
                                                                                                                                                                                          ww8
                                                                                                                                                                                          PendingTxIn
                                                                                                                                                                                          (lam
                                                                                                                                                                                            ww9
                                                                                                                                                                                            [Interval (con integer)]
                                                                                                                                                                                            (lam
                                                                                                                                                                                              ww10
                                                                                                                                                                                              [List [[Tuple2 (con bytestring)] (con bytestring)]]
                                                                                                                                                                                              (lam
                                                                                                                                                                                                ww11
                                                                                                                                                                                                (con bytestring)
                                                                                                                                                                                                [
                                                                                                                                                                                                  {
                                                                                                                                                                                                    [
                                                                                                                                                                                                      PendingTxIn_match
                                                                                                                                                                                                      ww8
                                                                                                                                                                                                    ]
                                                                                                                                                                                                    (con bytestring)
                                                                                                                                                                                                  }
                                                                                                                                                                                                  (lam
                                                                                                                                                                                                    ww13
                                                                                                                                                                                                    PendingTxOutRef
                                                                                                                                                                                                    (lam
                                                                                                                                                                                                      ww14
                                                                                                                                                                                                      [Maybe [[Tuple2 (con bytestring)] (con bytestring)]]
                                                                                                                                                                                                      (lam
                                                                                                                                                                                                        ww15
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
                                                                                                                                                                                                                  ww14
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
                                                                                                                                                                                                                      a1
                                                                                                                                                                                                                      (con bytestring)
                                                                                                                                                                                                                      (lam
                                                                                                                                                                                                                        ds2
                                                                                                                                                                                                                        (con bytestring)
                                                                                                                                                                                                                        a1
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
                                                                                                                                                                                                                    swmkValidator4
                                                                                                                                                                                                                  ]
                                                                                                                                                                                                                  (con bytestring)
                                                                                                                                                                                                                }
                                                                                                                                                                                                                (lam
                                                                                                                                                                                                                  a1
                                                                                                                                                                                                                  (con bytestring)
                                                                                                                                                                                                                  (lam
                                                                                                                                                                                                                    ds2
                                                                                                                                                                                                                    (con bytestring)
                                                                                                                                                                                                                    a1
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
                                                                                                                                                                                            )
                                                                                                                                                                                          )
                                                                                                                                                                                        )
                                                                                                                                                                                      )
                                                                                                                                                                                    )
                                                                                                                                                                                  )
                                                                                                                                                                                )
                                                                                                                                                                              ]
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
                                                                                                                                                                                    tn
                                                                                                                                                                                  ]
                                                                                                                                                                                  gameTokenVal5
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
                                                                                                                                                                    ]
                                                                                                                                                                  ]
                                                                                                                                                                  (fun Unit GameState)
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
                                                                                                                                                                                  equalsInteger
                                                                                                                                                                                ]
                                                                                                                                                                                {
                                                                                                                                                                                  Nil
                                                                                                                                                                                  [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                                                                                                                                }
                                                                                                                                                                              ]
                                                                                                                                                                              [
                                                                                                                                                                                pendingTxForge
                                                                                                                                                                                w
                                                                                                                                                                              ]
                                                                                                                                                                            ]
                                                                                                                                                                          ]
                                                                                                                                                                          (fun Unit GameState)
                                                                                                                                                                        }
                                                                                                                                                                        (lam
                                                                                                                                                                          thunk
                                                                                                                                                                          Unit
                                                                                                                                                                          [
                                                                                                                                                                            [
                                                                                                                                                                              Locked
                                                                                                                                                                              tn
                                                                                                                                                                            ]
                                                                                                                                                                            nextSecret
                                                                                                                                                                          ]
                                                                                                                                                                        )
                                                                                                                                                                      ]
                                                                                                                                                                      (lam
                                                                                                                                                                        thunk
                                                                                                                                                                        Unit
                                                                                                                                                                        mkValidator5
                                                                                                                                                                      )
                                                                                                                                                                    ]
                                                                                                                                                                    Unit
                                                                                                                                                                  ]
                                                                                                                                                                )
                                                                                                                                                              ]
                                                                                                                                                              (lam
                                                                                                                                                                thunk
                                                                                                                                                                Unit
                                                                                                                                                                mkValidator5
                                                                                                                                                              )
                                                                                                                                                            ]
                                                                                                                                                            Unit
                                                                                                                                                          ]
                                                                                                                                                        )
                                                                                                                                                      ]
                                                                                                                                                      (lam
                                                                                                                                                        thunk
                                                                                                                                                        Unit
                                                                                                                                                        mkValidator5
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
                                                                                                                                ww
                                                                                                                              ]
                                                                                                                              ww1
                                                                                                                            ]
                                                                                                                            ww2
                                                                                                                          ]
                                                                                                                          w
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
                                                                                                                    mkValidator
                                                                                                                    (fun [[Tuple2 GameState] [Maybe GameInput]] (fun [[Tuple2 GameState] [Maybe GameInput]] (fun PendingTx Bool)))
                                                                                                                  )
                                                                                                                  (lam
                                                                                                                    w
                                                                                                                    [[Tuple2 GameState] [Maybe GameInput]]
                                                                                                                    (lam
                                                                                                                      w5
                                                                                                                      [[Tuple2 GameState] [Maybe GameInput]]
                                                                                                                      (lam
                                                                                                                        w6
                                                                                                                        PendingTx
                                                                                                                        [
                                                                                                                          {
                                                                                                                            [
                                                                                                                              {
                                                                                                                                {
                                                                                                                                  Tuple2_match
                                                                                                                                  GameState
                                                                                                                                }
                                                                                                                                [Maybe GameInput]
                                                                                                                              }
                                                                                                                              w
                                                                                                                            ]
                                                                                                                            Bool
                                                                                                                          }
                                                                                                                          (lam
                                                                                                                            ww1
                                                                                                                            GameState
                                                                                                                            (lam
                                                                                                                              ww2
                                                                                                                              [Maybe GameInput]
                                                                                                                              [
                                                                                                                                {
                                                                                                                                  [
                                                                                                                                    {
                                                                                                                                      {
                                                                                                                                        Tuple2_match
                                                                                                                                        GameState
                                                                                                                                      }
                                                                                                                                      [Maybe GameInput]
                                                                                                                                    }
                                                                                                                                    w5
                                                                                                                                  ]
                                                                                                                                  Bool
                                                                                                                                }
                                                                                                                                (lam
                                                                                                                                  ww4
                                                                                                                                  GameState
                                                                                                                                  (lam
                                                                                                                                    ww5
                                                                                                                                    [Maybe GameInput]
                                                                                                                                    [
                                                                                                                                      [
                                                                                                                                        [
                                                                                                                                          [
                                                                                                                                            wmkValidator
                                                                                                                                            ww1
                                                                                                                                          ]
                                                                                                                                          ww4
                                                                                                                                        ]
                                                                                                                                        ww5
                                                                                                                                      ]
                                                                                                                                      w6
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