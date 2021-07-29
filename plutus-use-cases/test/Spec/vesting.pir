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
          (datatype
            (tyvardecl Bool (type))

            Bool_match
            (vardecl True Bool) (vardecl False Bool)
          )
        )
        (termbind
          (strict)
          (vardecl
            addInteger (fun (con integer) (fun (con integer) (con integer)))
          )
          (lam
            x
            (con integer)
            (lam y (con integer) [ [ (builtin addInteger) x ] y ])
          )
        )
        (termbind
          (strict)
          (vardecl
            equalsByteString (fun (con bytestring) (fun (con bytestring) Bool))
          )
          (lam
            x
            (con bytestring)
            (lam
              y
              (con bytestring)
              [
                [
                  [
                    { (builtin ifThenElse) Bool }
                    [ [ (builtin equalsByteString) x ] y ]
                  ]
                  True
                ]
                False
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
              (force
                [
                  [ { [ Bool_match ds ] (delayed Bool) } (delay True) ]
                  (delay ds)
                ]
              )
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
                  [ { Monoid_match a } v ] [(lam a (type) (fun a (fun a a))) a]
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
            (strict)
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
                      (vardecl dSemigroup [(lam a (type) (fun a (fun a a))) m])
                      [ { p1Monoid m } dMonoid ]
                    )
                    (lam
                      ds
                      (fun a m)
                      (lam
                        ds
                        [List a]
                        (force
                          [
                            [
                              { [ { Nil_match a } ds ] (delayed m) }
                              (delay [ { mempty m } dMonoid ])
                            ]
                            (lam
                              x
                              a
                              (lam
                                xs
                                [List a]
                                (delay
                                  [
                                    [ dSemigroup [ ds x ] ]
                                    [
                                      [
                                        [
                                          { { fFoldableNil_cfoldMap m } a }
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
                        )
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
                      (force
                        [
                          [
                            { [ { Nil_match a } l ] (delayed [List b]) }
                            (delay { Nil b })
                          ]
                          (lam
                            x
                            a
                            (lam
                              xs
                              [List a]
                              (delay
                                [
                                  [ { Cons b } [ f x ] ]
                                  [ [ { { fFunctorNil_cfmap a } b } f ] xs ]
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
                            (force
                              [
                                [
                                  { [ { Nil_match a } l ] (delayed b) }
                                  (delay acc)
                                ]
                                (lam
                                  x
                                  a
                                  (lam
                                    xs
                                    [List a]
                                    (delay
                                      [
                                        [ f x ]
                                        [ [ [ { { foldr a } b } f ] acc ] xs ]
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
                                          ds
                                          [[Tuple2 k] r]
                                          [
                                            {
                                              [ { { Tuple2_match k } r } ds ]
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
                                                [
                                                  {
                                                    [
                                                      { { Tuple2_match k } r } e
                                                    ]
                                                    [List [[Tuple2 k] r]]
                                                  }
                                                  (lam
                                                    c
                                                    k
                                                    (lam
                                                      ds
                                                      r
                                                      (force
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
                                                              (delayed [List [[Tuple2 k] r]])
                                                            }
                                                            (delay xs)
                                                          ]
                                                          (delay
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
                                                      )
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
                                                    (force
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
                                                            (delayed [[These v] r])
                                                          }
                                                          (delay
                                                            [
                                                              { { This v } r } i
                                                            ]
                                                          )
                                                        ]
                                                        (lam
                                                          ds
                                                          [[Tuple2 k] r]
                                                          (lam
                                                            xs
                                                            [List [[Tuple2 k] r]]
                                                            (delay
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
                                                                    (force
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
                                                                            (delayed [[These v] r])
                                                                          }
                                                                          (delay
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
                                                                        (delay
                                                                          [
                                                                            go
                                                                            xs
                                                                          ]
                                                                        )
                                                                      ]
                                                                    )
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
                                                [
                                                  [
                                                    {
                                                      { Tuple2 k } [[These v] r]
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
                              (force
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
                                      (delayed [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]]])
                                    }
                                    (delay
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
                                      (delay
                                        [
                                          {
                                            [
                                              {
                                                {
                                                  Tuple2_match (con bytestring)
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
                                                                  (force
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
                                                                          (delayed [List [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]])
                                                                        }
                                                                        (delay
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
                                                                          (delay
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
                                                                  )
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
                                                              (force
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
                                                                      (delayed [List [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]])
                                                                    }
                                                                    (delay
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
                                                                      (delay
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
                                                              )
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
                              )
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
                                (force
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
                                        (delayed [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]])
                                      }
                                      (delay
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
                                        (delay
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
                                                      (force
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
                                                              (delayed [List [[Tuple2 (con bytestring)] (con integer)]])
                                                            }
                                                            (delay
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
                                                              (delay
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
                                                      )
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
                                )
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
                    [ unionWith addInteger ]
                  )
                  (datatypebind
                    (datatype
                      (tyvardecl VestingTranche (type))

                      VestingTranche_match
                      (vardecl
                        VestingTranche
                        (fun (con integer) (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] VestingTranche))
                      )
                    )
                  )
                  (datatypebind
                    (datatype
                      (tyvardecl VestingParams (type))

                      VestingParams_match
                      (vardecl
                        VestingParams
                        (fun VestingTranche (fun VestingTranche (fun (con bytestring) VestingParams)))
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
                                (force
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
                                        (delayed Bool)
                                      }
                                      (delay True)
                                    ]
                                    (lam
                                      ds
                                      [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]]
                                      (lam
                                        xs
                                        [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[These (con integer)] (con integer)]]]]
                                        (delay
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
                                                      (force
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
                                                              (delayed Bool)
                                                            }
                                                            (delay [ go xs ])
                                                          ]
                                                          (lam
                                                            ds
                                                            [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]
                                                            (lam
                                                              xs
                                                              [List [[Tuple2 (con bytestring)] [[These (con integer)] (con integer)]]]
                                                              (delay
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
                                                                              (force
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
                                                                                      (delayed Bool)
                                                                                    }
                                                                                    (delay
                                                                                      [
                                                                                        go
                                                                                        xs
                                                                                      ]
                                                                                    )
                                                                                  ]
                                                                                  (delay
                                                                                    False
                                                                                  )
                                                                                ]
                                                                              )
                                                                            )
                                                                          ]
                                                                          (lam
                                                                            a
                                                                            (con integer)
                                                                            (lam
                                                                              b
                                                                              (con integer)
                                                                              (force
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
                                                                                      (delayed Bool)
                                                                                    }
                                                                                    (delay
                                                                                      [
                                                                                        go
                                                                                        xs
                                                                                      ]
                                                                                    )
                                                                                  ]
                                                                                  (delay
                                                                                    False
                                                                                  )
                                                                                ]
                                                                              )
                                                                            )
                                                                          )
                                                                        ]
                                                                        (lam
                                                                          a
                                                                          (con integer)
                                                                          (force
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
                                                                                  (delayed Bool)
                                                                                }
                                                                                (delay
                                                                                  [
                                                                                    go
                                                                                    xs
                                                                                  ]
                                                                                )
                                                                              ]
                                                                              (delay
                                                                                False
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
                                                        ]
                                                      )
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
                                )
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
                              (rec)
                              (termbind
                                (strict)
                                (vardecl go (fun [List a] b))
                                (lam
                                  ds
                                  [List a]
                                  (force
                                    [
                                      [
                                        { [ { Nil_match a } ds ] (delayed b) }
                                        (delay z)
                                      ]
                                      (lam
                                        y
                                        a
                                        (lam
                                          ys
                                          [List a]
                                          (delay [ [ k y ] [ go ys ] ])
                                        )
                                      )
                                    ]
                                  )
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
                              (force
                                [
                                  [
                                    { [ { Nil_match a } l ] (delayed [List b]) }
                                    (delay { Nil b })
                                  ]
                                  (lam
                                    x
                                    a
                                    (lam
                                      xs
                                      [List a]
                                      (delay
                                        [
                                          [ { Cons b } [ f x ] ]
                                          [ [ { { map a } b } f ] xs ]
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
                    (let
                      (nonrec)
                      (termbind
                        (strict)
                        (vardecl error (all a (type) (fun (con unit) a)))
                        (abs a (type) (lam thunk (con unit) (error a)))
                      )
                      (datatypebind
                        (datatype
                          (tyvardecl Unit (type))

                          Unit_match
                          (vardecl Unit Unit)
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
                      (termbind
                        (strict)
                        (vardecl
                          fEqTxOutRef_c (fun TxOutRef (fun TxOutRef Bool))
                        )
                        (lam
                          l
                          TxOutRef
                          (lam
                            r
                            TxOutRef
                            (force
                              [
                                [
                                  {
                                    [
                                      Bool_match
                                      [
                                        [
                                          [
                                            { (builtin ifThenElse) Bool }
                                            [
                                              [
                                                (builtin equalsByteString)
                                                [
                                                  {
                                                    [ TxOutRef_match l ]
                                                    (con bytestring)
                                                  }
                                                  (lam
                                                    ds
                                                    (con bytestring)
                                                    (lam ds (con integer) ds)
                                                  )
                                                ]
                                              ]
                                              [
                                                {
                                                  [ TxOutRef_match r ]
                                                  (con bytestring)
                                                }
                                                (lam
                                                  ds
                                                  (con bytestring)
                                                  (lam ds (con integer) ds)
                                                )
                                              ]
                                            ]
                                          ]
                                          True
                                        ]
                                        False
                                      ]
                                    ]
                                    (delayed Bool)
                                  }
                                  (delay
                                    [
                                      [
                                        [
                                          { (builtin ifThenElse) Bool }
                                          [
                                            [
                                              (builtin equalsInteger)
                                              [
                                                {
                                                  [ TxOutRef_match l ]
                                                  (con integer)
                                                }
                                                (lam
                                                  ds
                                                  (con bytestring)
                                                  (lam ds (con integer) ds)
                                                )
                                              ]
                                            ]
                                            [
                                              {
                                                [ TxOutRef_match r ]
                                                (con integer)
                                              }
                                              (lam
                                                ds
                                                (con bytestring)
                                                (lam ds (con integer) ds)
                                              )
                                            ]
                                          ]
                                        ]
                                        True
                                      ]
                                      False
                                    ]
                                  )
                                ]
                                (delay False)
                              ]
                            )
                          )
                        )
                      )
                      (datatypebind
                        (datatype
                          (tyvardecl Credential (type))

                          Credential_match
                          (vardecl
                            PubKeyCredential (fun (con bytestring) Credential)
                          )
                          (vardecl
                            ScriptCredential (fun (con bytestring) Credential)
                          )
                        )
                      )
                      (datatypebind
                        (datatype
                          (tyvardecl StakingCredential (type))

                          StakingCredential_match
                          (vardecl
                            StakingHash (fun Credential StakingCredential)
                          )
                          (vardecl
                            StakingPtr
                            (fun (con integer) (fun (con integer) (fun (con integer) StakingCredential)))
                          )
                        )
                      )
                      (datatypebind
                        (datatype
                          (tyvardecl DCert (type))

                          DCert_match
                          (vardecl
                            DCertDelegDeRegKey (fun StakingCredential DCert)
                          )
                          (vardecl
                            DCertDelegDelegate
                            (fun StakingCredential (fun (con bytestring) DCert))
                          )
                          (vardecl
                            DCertDelegRegKey (fun StakingCredential DCert)
                          )
                          (vardecl DCertGenesis DCert)
                          (vardecl DCertMir DCert)
                          (vardecl
                            DCertPoolRegister
                            (fun (con bytestring) (fun (con bytestring) DCert))
                          )
                          (vardecl
                            DCertPoolRetire
                            (fun (con bytestring) (fun (con integer) DCert))
                          )
                        )
                      )
                      (datatypebind
                        (datatype
                          (tyvardecl ScriptPurpose (type))

                          ScriptPurpose_match
                          (vardecl Certifying (fun DCert ScriptPurpose))
                          (vardecl Minting (fun (con bytestring) ScriptPurpose))
                          (vardecl
                            Rewarding (fun StakingCredential ScriptPurpose)
                          )
                          (vardecl Spending (fun TxOutRef ScriptPurpose))
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
                          (vardecl
                            LowerBound
                            (fun [Extended a] (fun Bool [LowerBound a]))
                          )
                        )
                      )
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
                          (tyvardecl Maybe (fun (type) (type)))
                          (tyvardecl a (type))
                          Maybe_match
                          (vardecl Just (fun a [Maybe a]))
                          (vardecl Nothing [Maybe a])
                        )
                      )
                      (datatypebind
                        (datatype
                          (tyvardecl Address (type))

                          Address_match
                          (vardecl
                            Address
                            (fun Credential (fun [Maybe StakingCredential] Address))
                          )
                        )
                      )
                      (datatypebind
                        (datatype
                          (tyvardecl TxOut (type))

                          TxOut_match
                          (vardecl
                            TxOut
                            (fun Address (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun [Maybe (con bytestring)] TxOut)))
                          )
                        )
                      )
                      (datatypebind
                        (datatype
                          (tyvardecl TxInInfo (type))

                          TxInInfo_match
                          (vardecl TxInInfo (fun TxOutRef (fun TxOut TxInInfo)))
                        )
                      )
                      (datatypebind
                        (datatype
                          (tyvardecl TxInfo (type))

                          TxInfo_match
                          (vardecl
                            TxInfo
                            (fun [List TxInInfo] (fun [List TxOut] (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun [List DCert] (fun [List [[Tuple2 StakingCredential] (con integer)]] (fun [Interval (con integer)] (fun [List (con bytestring)] (fun [List [[Tuple2 (con bytestring)] (con data)]] (fun (con bytestring) TxInfo))))))))))
                          )
                        )
                      )
                      (datatypebind
                        (datatype
                          (tyvardecl ScriptContext (type))

                          ScriptContext_match
                          (vardecl
                            ScriptContext
                            (fun TxInfo (fun ScriptPurpose ScriptContext))
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
                              (force
                                [
                                  [
                                    {
                                      [ { Maybe_match a } ds ]
                                      (delayed [(lam a (type) [Maybe a]) a])
                                    }
                                    (lam ipv a (delay ds))
                                  ]
                                  (delay b)
                                ]
                              )
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
                          findOwnInput (fun ScriptContext [Maybe TxInInfo])
                        )
                        (lam
                          ds
                          ScriptContext
                          [
                            { [ ScriptContext_match ds ] [Maybe TxInInfo] }
                            (lam
                              ds
                              TxInfo
                              (lam
                                ds
                                ScriptPurpose
                                [
                                  { [ TxInfo_match ds ] [Maybe TxInInfo] }
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
                                            [List DCert]
                                            (lam
                                              ds
                                              [List [[Tuple2 StakingCredential] (con integer)]]
                                              (lam
                                                ds
                                                [Interval (con integer)]
                                                (lam
                                                  ds
                                                  [List (con bytestring)]
                                                  (lam
                                                    ds
                                                    [List [[Tuple2 (con bytestring)] (con data)]]
                                                    (lam
                                                      ds
                                                      (con bytestring)
                                                      (force
                                                        [
                                                          [
                                                            [
                                                              [
                                                                {
                                                                  [
                                                                    ScriptPurpose_match
                                                                    ds
                                                                  ]
                                                                  (delayed [Maybe TxInInfo])
                                                                }
                                                                (lam
                                                                  default_arg0
                                                                  DCert
                                                                  (delay
                                                                    {
                                                                      Nothing
                                                                      TxInInfo
                                                                    }
                                                                  )
                                                                )
                                                              ]
                                                              (lam
                                                                default_arg0
                                                                (con bytestring)
                                                                (delay
                                                                  {
                                                                    Nothing
                                                                    TxInInfo
                                                                  }
                                                                )
                                                              )
                                                            ]
                                                            (lam
                                                              default_arg0
                                                              StakingCredential
                                                              (delay
                                                                {
                                                                  Nothing
                                                                  TxInInfo
                                                                }
                                                              )
                                                            )
                                                          ]
                                                          (lam
                                                            txOutRef
                                                            TxOutRef
                                                            (delay
                                                              [
                                                                [
                                                                  [
                                                                    {
                                                                      {
                                                                        fFoldableNil_cfoldMap
                                                                        [(lam a (type) [Maybe a]) TxInInfo]
                                                                      }
                                                                      TxInInfo
                                                                    }
                                                                    {
                                                                      fMonoidFirst
                                                                      TxInInfo
                                                                    }
                                                                  ]
                                                                  (lam
                                                                    x
                                                                    TxInInfo
                                                                    [
                                                                      {
                                                                        [
                                                                          TxInInfo_match
                                                                          x
                                                                        ]
                                                                        [Maybe TxInInfo]
                                                                      }
                                                                      (lam
                                                                        ds
                                                                        TxOutRef
                                                                        (lam
                                                                          ds
                                                                          TxOut
                                                                          (force
                                                                            [
                                                                              [
                                                                                {
                                                                                  [
                                                                                    Bool_match
                                                                                    [
                                                                                      [
                                                                                        fEqTxOutRef_c
                                                                                        ds
                                                                                      ]
                                                                                      txOutRef
                                                                                    ]
                                                                                  ]
                                                                                  (delayed [Maybe TxInInfo])
                                                                                }
                                                                                (delay
                                                                                  [
                                                                                    {
                                                                                      Just
                                                                                      TxInInfo
                                                                                    }
                                                                                    x
                                                                                  ]
                                                                                )
                                                                              ]
                                                                              (delay
                                                                                {
                                                                                  Nothing
                                                                                  TxInInfo
                                                                                }
                                                                              )
                                                                            ]
                                                                          )
                                                                        )
                                                                      )
                                                                    ]
                                                                  )
                                                                ]
                                                                ds
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
                      (termbind
                        (strict)
                        (vardecl
                          ownHashes
                          (fun ScriptContext [[Tuple2 (con bytestring)] (con bytestring)])
                        )
                        (lam
                          ds
                          ScriptContext
                          (let
                            (nonrec)
                            (termbind
                              (strict)
                              (vardecl
                                fail
                                (fun (all a (type) a) [[Tuple2 (con bytestring)] (con bytestring)])
                              )
                              (lam
                                ds
                                (all a (type) a)
                                [
                                  {
                                    error
                                    [[Tuple2 (con bytestring)] (con bytestring)]
                                  }
                                  [
                                    {
                                      [
                                        Unit_match
                                        [
                                          [
                                            { (builtin chooseUnit) Unit }
                                            [
                                              (builtin trace)
                                              (con
                                                string
                                                  "Can't get validator and datum hashes"
                                              )
                                            ]
                                          ]
                                          Unit
                                        ]
                                      ]
                                      (con unit)
                                    }
                                    (con unit ())
                                  ]
                                ]
                              )
                            )
                            (force
                              [
                                [
                                  {
                                    [
                                      { Maybe_match TxInInfo }
                                      [ findOwnInput ds ]
                                    ]
                                    (delayed [[Tuple2 (con bytestring)] (con bytestring)])
                                  }
                                  (lam
                                    ds
                                    TxInInfo
                                    (delay
                                      [
                                        {
                                          [ TxInInfo_match ds ]
                                          [[Tuple2 (con bytestring)] (con bytestring)]
                                        }
                                        (lam
                                          ds
                                          TxOutRef
                                          (lam
                                            ds
                                            TxOut
                                            [
                                              {
                                                [ TxOut_match ds ]
                                                [[Tuple2 (con bytestring)] (con bytestring)]
                                              }
                                              (lam
                                                ds
                                                Address
                                                (lam
                                                  ds
                                                  [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                  (lam
                                                    ds
                                                    [Maybe (con bytestring)]
                                                    [
                                                      {
                                                        [ Address_match ds ]
                                                        [[Tuple2 (con bytestring)] (con bytestring)]
                                                      }
                                                      (lam
                                                        ds
                                                        Credential
                                                        (lam
                                                          ds
                                                          [Maybe StakingCredential]
                                                          [
                                                            [
                                                              {
                                                                [
                                                                  Credential_match
                                                                  ds
                                                                ]
                                                                [[Tuple2 (con bytestring)] (con bytestring)]
                                                              }
                                                              (lam
                                                                ipv
                                                                (con bytestring)
                                                                [
                                                                  fail
                                                                  (abs
                                                                    e
                                                                    (type)
                                                                    (error e)
                                                                  )
                                                                ]
                                                              )
                                                            ]
                                                            (lam
                                                              s
                                                              (con bytestring)
                                                              (force
                                                                [
                                                                  [
                                                                    {
                                                                      [
                                                                        {
                                                                          Maybe_match
                                                                          (con bytestring)
                                                                        }
                                                                        ds
                                                                      ]
                                                                      (delayed [[Tuple2 (con bytestring)] (con bytestring)])
                                                                    }
                                                                    (lam
                                                                      dh
                                                                      (con bytestring)
                                                                      (delay
                                                                        [
                                                                          [
                                                                            {
                                                                              {
                                                                                Tuple2
                                                                                (con bytestring)
                                                                              }
                                                                              (con bytestring)
                                                                            }
                                                                            s
                                                                          ]
                                                                          dh
                                                                        ]
                                                                      )
                                                                    )
                                                                  ]
                                                                  (delay
                                                                    [
                                                                      fail
                                                                      (abs
                                                                        e
                                                                        (type)
                                                                        (error e
                                                                        )
                                                                      )
                                                                    ]
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
                                            ]
                                          )
                                        )
                                      ]
                                    )
                                  )
                                ]
                                (delay [ fail (abs e (type) (error e)) ])
                              ]
                            )
                          )
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
                                  (force
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
                                          (delayed [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]])
                                        }
                                        (delay
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
                                          (delay
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
                                                        (force
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
                                                                (delayed [List [[Tuple2 (con bytestring)] (con integer)]])
                                                              }
                                                              (delay
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
                                                                (delay
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
                                                        )
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
                                  )
                                )
                              )
                              [ go ds ]
                            )
                          )
                        )
                      )
                      (datatypebind
                        (datatype
                          (tyvardecl Ordering (type))

                          Ordering_match
                          (vardecl EQ Ordering)
                          (vardecl GT Ordering)
                          (vardecl LT Ordering)
                        )
                      )
                      (termbind
                        (strict)
                        (vardecl
                          fOrdData_ccompare
                          (fun (con integer) (fun (con integer) Ordering))
                        )
                        (lam
                          x
                          (con integer)
                          (lam
                            y
                            (con integer)
                            (force
                              [
                                [
                                  {
                                    [
                                      Bool_match
                                      [
                                        [
                                          [
                                            { (builtin ifThenElse) Bool }
                                            [ [ (builtin equalsInteger) x ] y ]
                                          ]
                                          True
                                        ]
                                        False
                                      ]
                                    ]
                                    (delayed Ordering)
                                  }
                                  (delay EQ)
                                ]
                                (delay
                                  (force
                                    [
                                      [
                                        {
                                          [
                                            Bool_match
                                            [
                                              [
                                                [
                                                  { (builtin ifThenElse) Bool }
                                                  [
                                                    [
                                                      (builtin
                                                        lessThanEqualsInteger
                                                      )
                                                      x
                                                    ]
                                                    y
                                                  ]
                                                ]
                                                True
                                              ]
                                              False
                                            ]
                                          ]
                                          (delayed Ordering)
                                        }
                                        (delay LT)
                                      ]
                                      (delay GT)
                                    ]
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
                          fOrdInteger_cmax
                          (fun (con integer) (fun (con integer) (con integer)))
                        )
                        (lam
                          x
                          (con integer)
                          (lam
                            y
                            (con integer)
                            (force
                              [
                                [
                                  {
                                    [
                                      Bool_match
                                      [
                                        [
                                          [
                                            { (builtin ifThenElse) Bool }
                                            [
                                              [
                                                (builtin lessThanEqualsInteger)
                                                x
                                              ]
                                              y
                                            ]
                                          ]
                                          True
                                        ]
                                        False
                                      ]
                                    ]
                                    (delayed (con integer))
                                  }
                                  (delay y)
                                ]
                                (delay x)
                              ]
                            )
                          )
                        )
                      )
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
                            (force
                              [
                                [
                                  {
                                    [
                                      Bool_match
                                      [
                                        [
                                          [
                                            { (builtin ifThenElse) Bool }
                                            [
                                              [
                                                (builtin lessThanEqualsInteger)
                                                x
                                              ]
                                              y
                                            ]
                                          ]
                                          True
                                        ]
                                        False
                                      ]
                                    ]
                                    (delayed (con integer))
                                  }
                                  (delay x)
                                ]
                                (delay y)
                              ]
                            )
                          )
                        )
                      )
                      (termbind
                        (strict)
                        (vardecl
                          equalsInteger
                          (fun (con integer) (fun (con integer) Bool))
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
                                  { (builtin ifThenElse) Bool }
                                  [ [ (builtin equalsInteger) x ] y ]
                                ]
                                True
                              ]
                              False
                            ]
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
                          x
                          (con integer)
                          (lam
                            y
                            (con integer)
                            [
                              [
                                [
                                  { (builtin ifThenElse) Bool }
                                  [ [ (builtin greaterThanEqualsInteger) x ] y ]
                                ]
                                True
                              ]
                              False
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
                          x
                          (con integer)
                          (lam
                            y
                            (con integer)
                            [
                              [
                                [
                                  { (builtin ifThenElse) Bool }
                                  [ [ (builtin greaterThanInteger) x ] y ]
                                ]
                                True
                              ]
                              False
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
                          x
                          (con integer)
                          (lam
                            y
                            (con integer)
                            [
                              [
                                [
                                  { (builtin ifThenElse) Bool }
                                  [ [ (builtin lessThanEqualsInteger) x ] y ]
                                ]
                                True
                              ]
                              False
                            ]
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
                          x
                          (con integer)
                          (lam
                            y
                            (con integer)
                            [
                              [
                                [
                                  { (builtin ifThenElse) Bool }
                                  [ [ (builtin lessThanInteger) x ] y ]
                                ]
                                True
                              ]
                              False
                            ]
                          )
                        )
                      )
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
                      (termbind
                        (nonstrict)
                        (vardecl fOrdPOSIXTime [Ord (con integer)])
                        [
                          [
                            [
                              [
                                [
                                  [
                                    [
                                      [
                                        { CConsOrd (con integer) } equalsInteger
                                      ]
                                      fOrdData_ccompare
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
                      (termbind
                        (strict)
                        (vardecl
                          compare
                          (all a (type) (fun [Ord a] (fun a (fun a Ordering))))
                        )
                        (abs
                          a
                          (type)
                          (lam
                            v
                            [Ord a]
                            [
                              { [ { Ord_match a } v ] (fun a (fun a Ordering)) }
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
                                            (lam v (fun a (fun a a)) v)
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
                          hull_ccompare
                          (all a (type) (fun [Ord a] (fun [Extended a] (fun [Extended a] Ordering))))
                        )
                        (abs
                          a
                          (type)
                          (lam
                            dOrd
                            [Ord a]
                            (lam
                              ds
                              [Extended a]
                              (lam
                                ds
                                [Extended a]
                                (let
                                  (nonrec)
                                  (termbind
                                    (strict)
                                    (vardecl
                                      fail (fun (all a (type) a) Ordering)
                                    )
                                    (lam ds (all a (type) a) (error Ordering))
                                  )
                                  (termbind
                                    (strict)
                                    (vardecl
                                      fail (fun (all a (type) a) Ordering)
                                    )
                                    (lam
                                      ds
                                      (all a (type) a)
                                      (force
                                        [
                                          [
                                            [
                                              {
                                                [ { Extended_match a } ds ]
                                                (delayed Ordering)
                                              }
                                              (lam
                                                default_arg0
                                                a
                                                (delay
                                                  (force
                                                    [
                                                      [
                                                        [
                                                          {
                                                            [
                                                              {
                                                                Extended_match a
                                                              }
                                                              ds
                                                            ]
                                                            (delayed Ordering)
                                                          }
                                                          (lam
                                                            l
                                                            a
                                                            (delay
                                                              (force
                                                                [
                                                                  [
                                                                    [
                                                                      {
                                                                        [
                                                                          {
                                                                            Extended_match
                                                                            a
                                                                          }
                                                                          ds
                                                                        ]
                                                                        (delayed Ordering)
                                                                      }
                                                                      (lam
                                                                        r
                                                                        a
                                                                        (delay
                                                                          [
                                                                            [
                                                                              [
                                                                                {
                                                                                  compare
                                                                                  a
                                                                                }
                                                                                dOrd
                                                                              ]
                                                                              l
                                                                            ]
                                                                            r
                                                                          ]
                                                                        )
                                                                      )
                                                                    ]
                                                                    (delay
                                                                      [
                                                                        fail
                                                                        (abs
                                                                          e
                                                                          (type)
                                                                          (error
                                                                            e
                                                                          )
                                                                        )
                                                                      ]
                                                                    )
                                                                  ]
                                                                  (delay
                                                                    [
                                                                      fail
                                                                      (abs
                                                                        e
                                                                        (type)
                                                                        (error e
                                                                        )
                                                                      )
                                                                    ]
                                                                  )
                                                                ]
                                                              )
                                                            )
                                                          )
                                                        ]
                                                        (delay
                                                          [
                                                            fail
                                                            (abs
                                                              e (type) (error e)
                                                            )
                                                          ]
                                                        )
                                                      ]
                                                      (delay GT)
                                                    ]
                                                  )
                                                )
                                              )
                                            ]
                                            (delay
                                              (force
                                                [
                                                  [
                                                    [
                                                      {
                                                        [
                                                          { Extended_match a }
                                                          ds
                                                        ]
                                                        (delayed Ordering)
                                                      }
                                                      (lam
                                                        l
                                                        a
                                                        (delay
                                                          (force
                                                            [
                                                              [
                                                                [
                                                                  {
                                                                    [
                                                                      {
                                                                        Extended_match
                                                                        a
                                                                      }
                                                                      ds
                                                                    ]
                                                                    (delayed Ordering)
                                                                  }
                                                                  (lam
                                                                    r
                                                                    a
                                                                    (delay
                                                                      [
                                                                        [
                                                                          [
                                                                            {
                                                                              compare
                                                                              a
                                                                            }
                                                                            dOrd
                                                                          ]
                                                                          l
                                                                        ]
                                                                        r
                                                                      ]
                                                                    )
                                                                  )
                                                                ]
                                                                (delay
                                                                  [
                                                                    fail
                                                                    (abs
                                                                      e
                                                                      (type)
                                                                      (error e)
                                                                    )
                                                                  ]
                                                                )
                                                              ]
                                                              (delay
                                                                [
                                                                  fail
                                                                  (abs
                                                                    e
                                                                    (type)
                                                                    (error e)
                                                                  )
                                                                ]
                                                              )
                                                            ]
                                                          )
                                                        )
                                                      )
                                                    ]
                                                    (delay
                                                      [
                                                        fail
                                                        (abs e (type) (error e))
                                                      ]
                                                    )
                                                  ]
                                                  (delay GT)
                                                ]
                                              )
                                            )
                                          ]
                                          (delay LT)
                                        ]
                                      )
                                    )
                                  )
                                  (force
                                    [
                                      [
                                        [
                                          {
                                            [ { Extended_match a } ds ]
                                            (delayed Ordering)
                                          }
                                          (lam
                                            default_arg0
                                            a
                                            (let
                                              (nonrec)
                                              (termbind
                                                (strict)
                                                (vardecl
                                                  fail
                                                  (fun (all a (type) a) Ordering)
                                                )
                                                (lam
                                                  ds
                                                  (all a (type) a)
                                                  (force
                                                    [
                                                      [
                                                        [
                                                          {
                                                            [
                                                              {
                                                                Extended_match a
                                                              }
                                                              ds
                                                            ]
                                                            (delayed Ordering)
                                                          }
                                                          (lam
                                                            default_arg0
                                                            a
                                                            (delay
                                                              (force
                                                                [
                                                                  [
                                                                    [
                                                                      {
                                                                        [
                                                                          {
                                                                            Extended_match
                                                                            a
                                                                          }
                                                                          ds
                                                                        ]
                                                                        (delayed Ordering)
                                                                      }
                                                                      (lam
                                                                        l
                                                                        a
                                                                        (delay
                                                                          (force
                                                                            [
                                                                              [
                                                                                [
                                                                                  {
                                                                                    [
                                                                                      {
                                                                                        Extended_match
                                                                                        a
                                                                                      }
                                                                                      ds
                                                                                    ]
                                                                                    (delayed Ordering)
                                                                                  }
                                                                                  (lam
                                                                                    r
                                                                                    a
                                                                                    (delay
                                                                                      [
                                                                                        [
                                                                                          [
                                                                                            {
                                                                                              compare
                                                                                              a
                                                                                            }
                                                                                            dOrd
                                                                                          ]
                                                                                          l
                                                                                        ]
                                                                                        r
                                                                                      ]
                                                                                    )
                                                                                  )
                                                                                ]
                                                                                (delay
                                                                                  [
                                                                                    fail
                                                                                    (abs
                                                                                      e
                                                                                      (type)
                                                                                      (error
                                                                                        e
                                                                                      )
                                                                                    )
                                                                                  ]
                                                                                )
                                                                              ]
                                                                              (delay
                                                                                [
                                                                                  fail
                                                                                  (abs
                                                                                    e
                                                                                    (type)
                                                                                    (error
                                                                                      e
                                                                                    )
                                                                                  )
                                                                                ]
                                                                              )
                                                                            ]
                                                                          )
                                                                        )
                                                                      )
                                                                    ]
                                                                    (delay
                                                                      [
                                                                        fail
                                                                        (abs
                                                                          e
                                                                          (type)
                                                                          (error
                                                                            e
                                                                          )
                                                                        )
                                                                      ]
                                                                    )
                                                                  ]
                                                                  (delay GT)
                                                                ]
                                                              )
                                                            )
                                                          )
                                                        ]
                                                        (delay
                                                          (force
                                                            [
                                                              [
                                                                [
                                                                  {
                                                                    [
                                                                      {
                                                                        Extended_match
                                                                        a
                                                                      }
                                                                      ds
                                                                    ]
                                                                    (delayed Ordering)
                                                                  }
                                                                  (lam
                                                                    l
                                                                    a
                                                                    (delay
                                                                      (force
                                                                        [
                                                                          [
                                                                            [
                                                                              {
                                                                                [
                                                                                  {
                                                                                    Extended_match
                                                                                    a
                                                                                  }
                                                                                  ds
                                                                                ]
                                                                                (delayed Ordering)
                                                                              }
                                                                              (lam
                                                                                r
                                                                                a
                                                                                (delay
                                                                                  [
                                                                                    [
                                                                                      [
                                                                                        {
                                                                                          compare
                                                                                          a
                                                                                        }
                                                                                        dOrd
                                                                                      ]
                                                                                      l
                                                                                    ]
                                                                                    r
                                                                                  ]
                                                                                )
                                                                              )
                                                                            ]
                                                                            (delay
                                                                              [
                                                                                fail
                                                                                (abs
                                                                                  e
                                                                                  (type)
                                                                                  (error
                                                                                    e
                                                                                  )
                                                                                )
                                                                              ]
                                                                            )
                                                                          ]
                                                                          (delay
                                                                            [
                                                                              fail
                                                                              (abs
                                                                                e
                                                                                (type)
                                                                                (error
                                                                                  e
                                                                                )
                                                                              )
                                                                            ]
                                                                          )
                                                                        ]
                                                                      )
                                                                    )
                                                                  )
                                                                ]
                                                                (delay
                                                                  [
                                                                    fail
                                                                    (abs
                                                                      e
                                                                      (type)
                                                                      (error e)
                                                                    )
                                                                  ]
                                                                )
                                                              ]
                                                              (delay GT)
                                                            ]
                                                          )
                                                        )
                                                      ]
                                                      (delay LT)
                                                    ]
                                                  )
                                                )
                                              )
                                              (delay
                                                (force
                                                  [
                                                    [
                                                      [
                                                        {
                                                          [
                                                            { Extended_match a }
                                                            ds
                                                          ]
                                                          (delayed Ordering)
                                                        }
                                                        (lam
                                                          default_arg0
                                                          a
                                                          (let
                                                            (nonrec)
                                                            (termbind
                                                              (strict)
                                                              (vardecl
                                                                fail
                                                                (fun (all a (type) a) Ordering)
                                                              )
                                                              (lam
                                                                ds
                                                                (all a (type) a)
                                                                (force
                                                                  [
                                                                    [
                                                                      [
                                                                        {
                                                                          [
                                                                            {
                                                                              Extended_match
                                                                              a
                                                                            }
                                                                            ds
                                                                          ]
                                                                          (delayed Ordering)
                                                                        }
                                                                        (lam
                                                                          default_arg0
                                                                          a
                                                                          (delay
                                                                            (force
                                                                              [
                                                                                [
                                                                                  [
                                                                                    {
                                                                                      [
                                                                                        {
                                                                                          Extended_match
                                                                                          a
                                                                                        }
                                                                                        ds
                                                                                      ]
                                                                                      (delayed Ordering)
                                                                                    }
                                                                                    (lam
                                                                                      l
                                                                                      a
                                                                                      (delay
                                                                                        (force
                                                                                          [
                                                                                            [
                                                                                              [
                                                                                                {
                                                                                                  [
                                                                                                    {
                                                                                                      Extended_match
                                                                                                      a
                                                                                                    }
                                                                                                    ds
                                                                                                  ]
                                                                                                  (delayed Ordering)
                                                                                                }
                                                                                                (lam
                                                                                                  r
                                                                                                  a
                                                                                                  (delay
                                                                                                    [
                                                                                                      [
                                                                                                        [
                                                                                                          {
                                                                                                            compare
                                                                                                            a
                                                                                                          }
                                                                                                          dOrd
                                                                                                        ]
                                                                                                        l
                                                                                                      ]
                                                                                                      r
                                                                                                    ]
                                                                                                  )
                                                                                                )
                                                                                              ]
                                                                                              (delay
                                                                                                [
                                                                                                  fail
                                                                                                  (abs
                                                                                                    e
                                                                                                    (type)
                                                                                                    (error
                                                                                                      e
                                                                                                    )
                                                                                                  )
                                                                                                ]
                                                                                              )
                                                                                            ]
                                                                                            (delay
                                                                                              [
                                                                                                fail
                                                                                                (abs
                                                                                                  e
                                                                                                  (type)
                                                                                                  (error
                                                                                                    e
                                                                                                  )
                                                                                                )
                                                                                              ]
                                                                                            )
                                                                                          ]
                                                                                        )
                                                                                      )
                                                                                    )
                                                                                  ]
                                                                                  (delay
                                                                                    [
                                                                                      fail
                                                                                      (abs
                                                                                        e
                                                                                        (type)
                                                                                        (error
                                                                                          e
                                                                                        )
                                                                                      )
                                                                                    ]
                                                                                  )
                                                                                ]
                                                                                (delay
                                                                                  GT
                                                                                )
                                                                              ]
                                                                            )
                                                                          )
                                                                        )
                                                                      ]
                                                                      (delay
                                                                        (force
                                                                          [
                                                                            [
                                                                              [
                                                                                {
                                                                                  [
                                                                                    {
                                                                                      Extended_match
                                                                                      a
                                                                                    }
                                                                                    ds
                                                                                  ]
                                                                                  (delayed Ordering)
                                                                                }
                                                                                (lam
                                                                                  l
                                                                                  a
                                                                                  (delay
                                                                                    (force
                                                                                      [
                                                                                        [
                                                                                          [
                                                                                            {
                                                                                              [
                                                                                                {
                                                                                                  Extended_match
                                                                                                  a
                                                                                                }
                                                                                                ds
                                                                                              ]
                                                                                              (delayed Ordering)
                                                                                            }
                                                                                            (lam
                                                                                              r
                                                                                              a
                                                                                              (delay
                                                                                                [
                                                                                                  [
                                                                                                    [
                                                                                                      {
                                                                                                        compare
                                                                                                        a
                                                                                                      }
                                                                                                      dOrd
                                                                                                    ]
                                                                                                    l
                                                                                                  ]
                                                                                                  r
                                                                                                ]
                                                                                              )
                                                                                            )
                                                                                          ]
                                                                                          (delay
                                                                                            [
                                                                                              fail
                                                                                              (abs
                                                                                                e
                                                                                                (type)
                                                                                                (error
                                                                                                  e
                                                                                                )
                                                                                              )
                                                                                            ]
                                                                                          )
                                                                                        ]
                                                                                        (delay
                                                                                          [
                                                                                            fail
                                                                                            (abs
                                                                                              e
                                                                                              (type)
                                                                                              (error
                                                                                                e
                                                                                              )
                                                                                            )
                                                                                          ]
                                                                                        )
                                                                                      ]
                                                                                    )
                                                                                  )
                                                                                )
                                                                              ]
                                                                              (delay
                                                                                [
                                                                                  fail
                                                                                  (abs
                                                                                    e
                                                                                    (type)
                                                                                    (error
                                                                                      e
                                                                                    )
                                                                                  )
                                                                                ]
                                                                              )
                                                                            ]
                                                                            (delay
                                                                              GT
                                                                            )
                                                                          ]
                                                                        )
                                                                      )
                                                                    ]
                                                                    (delay LT)
                                                                  ]
                                                                )
                                                              )
                                                            )
                                                            (delay
                                                              (force
                                                                [
                                                                  [
                                                                    [
                                                                      {
                                                                        [
                                                                          {
                                                                            Extended_match
                                                                            a
                                                                          }
                                                                          ds
                                                                        ]
                                                                        (delayed Ordering)
                                                                      }
                                                                      (lam
                                                                        default_arg0
                                                                        a
                                                                        (delay
                                                                          [
                                                                            fail
                                                                            (abs
                                                                              e
                                                                              (type)
                                                                              (error
                                                                                e
                                                                              )
                                                                            )
                                                                          ]
                                                                        )
                                                                      )
                                                                    ]
                                                                    (delay
                                                                      [
                                                                        fail
                                                                        (abs
                                                                          e
                                                                          (type)
                                                                          (error
                                                                            e
                                                                          )
                                                                        )
                                                                      ]
                                                                    )
                                                                  ]
                                                                  (delay
                                                                    (force
                                                                      [
                                                                        [
                                                                          [
                                                                            {
                                                                              [
                                                                                {
                                                                                  Extended_match
                                                                                  a
                                                                                }
                                                                                ds
                                                                              ]
                                                                              (delayed Ordering)
                                                                            }
                                                                            (lam
                                                                              default_arg0
                                                                              a
                                                                              (delay
                                                                                [
                                                                                  fail
                                                                                  (abs
                                                                                    e
                                                                                    (type)
                                                                                    (error
                                                                                      e
                                                                                    )
                                                                                  )
                                                                                ]
                                                                              )
                                                                            )
                                                                          ]
                                                                          (delay
                                                                            [
                                                                              fail
                                                                              (abs
                                                                                e
                                                                                (type)
                                                                                (error
                                                                                  e
                                                                                )
                                                                              )
                                                                            ]
                                                                          )
                                                                        ]
                                                                        (delay
                                                                          EQ
                                                                        )
                                                                      ]
                                                                    )
                                                                  )
                                                                ]
                                                              )
                                                            )
                                                          )
                                                        )
                                                      ]
                                                      (delay GT)
                                                    ]
                                                    (delay
                                                      (force
                                                        [
                                                          [
                                                            [
                                                              {
                                                                [
                                                                  {
                                                                    Extended_match
                                                                    a
                                                                  }
                                                                  ds
                                                                ]
                                                                (delayed Ordering)
                                                              }
                                                              (lam
                                                                default_arg0
                                                                a
                                                                (delay
                                                                  [
                                                                    fail
                                                                    (abs
                                                                      e
                                                                      (type)
                                                                      (error e)
                                                                    )
                                                                  ]
                                                                )
                                                              )
                                                            ]
                                                            (delay
                                                              [
                                                                fail
                                                                (abs
                                                                  e
                                                                  (type)
                                                                  (error e)
                                                                )
                                                              ]
                                                            )
                                                          ]
                                                          (delay
                                                            (force
                                                              [
                                                                [
                                                                  [
                                                                    {
                                                                      [
                                                                        {
                                                                          Extended_match
                                                                          a
                                                                        }
                                                                        ds
                                                                      ]
                                                                      (delayed Ordering)
                                                                    }
                                                                    (lam
                                                                      default_arg0
                                                                      a
                                                                      (delay
                                                                        [
                                                                          fail
                                                                          (abs
                                                                            e
                                                                            (type)
                                                                            (error
                                                                              e
                                                                            )
                                                                          )
                                                                        ]
                                                                      )
                                                                    )
                                                                  ]
                                                                  (delay
                                                                    [
                                                                      fail
                                                                      (abs
                                                                        e
                                                                        (type)
                                                                        (error e
                                                                        )
                                                                      )
                                                                    ]
                                                                  )
                                                                ]
                                                                (delay EQ)
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
                                        ]
                                        (delay
                                          (force
                                            [
                                              [
                                                [
                                                  {
                                                    [ { Extended_match a } ds ]
                                                    (delayed Ordering)
                                                  }
                                                  (lam default_arg0 a (delay LT)
                                                  )
                                                ]
                                                (delay EQ)
                                              ]
                                              (delay LT)
                                            ]
                                          )
                                        )
                                      ]
                                      (delay
                                        (force
                                          [
                                            [
                                              [
                                                {
                                                  [ { Extended_match a } ds ]
                                                  (delayed Ordering)
                                                }
                                                (lam
                                                  default_arg0
                                                  a
                                                  (let
                                                    (nonrec)
                                                    (termbind
                                                      (strict)
                                                      (vardecl
                                                        fail
                                                        (fun (all a (type) a) Ordering)
                                                      )
                                                      (lam
                                                        ds
                                                        (all a (type) a)
                                                        (force
                                                          [
                                                            [
                                                              [
                                                                {
                                                                  [
                                                                    {
                                                                      Extended_match
                                                                      a
                                                                    }
                                                                    ds
                                                                  ]
                                                                  (delayed Ordering)
                                                                }
                                                                (lam
                                                                  default_arg0
                                                                  a
                                                                  (delay
                                                                    (force
                                                                      [
                                                                        [
                                                                          [
                                                                            {
                                                                              [
                                                                                {
                                                                                  Extended_match
                                                                                  a
                                                                                }
                                                                                ds
                                                                              ]
                                                                              (delayed Ordering)
                                                                            }
                                                                            (lam
                                                                              l
                                                                              a
                                                                              (delay
                                                                                (force
                                                                                  [
                                                                                    [
                                                                                      [
                                                                                        {
                                                                                          [
                                                                                            {
                                                                                              Extended_match
                                                                                              a
                                                                                            }
                                                                                            ds
                                                                                          ]
                                                                                          (delayed Ordering)
                                                                                        }
                                                                                        (lam
                                                                                          r
                                                                                          a
                                                                                          (delay
                                                                                            [
                                                                                              [
                                                                                                [
                                                                                                  {
                                                                                                    compare
                                                                                                    a
                                                                                                  }
                                                                                                  dOrd
                                                                                                ]
                                                                                                l
                                                                                              ]
                                                                                              r
                                                                                            ]
                                                                                          )
                                                                                        )
                                                                                      ]
                                                                                      (delay
                                                                                        [
                                                                                          fail
                                                                                          (abs
                                                                                            e
                                                                                            (type)
                                                                                            (error
                                                                                              e
                                                                                            )
                                                                                          )
                                                                                        ]
                                                                                      )
                                                                                    ]
                                                                                    (delay
                                                                                      [
                                                                                        fail
                                                                                        (abs
                                                                                          e
                                                                                          (type)
                                                                                          (error
                                                                                            e
                                                                                          )
                                                                                        )
                                                                                      ]
                                                                                    )
                                                                                  ]
                                                                                )
                                                                              )
                                                                            )
                                                                          ]
                                                                          (delay
                                                                            [
                                                                              fail
                                                                              (abs
                                                                                e
                                                                                (type)
                                                                                (error
                                                                                  e
                                                                                )
                                                                              )
                                                                            ]
                                                                          )
                                                                        ]
                                                                        (delay
                                                                          GT
                                                                        )
                                                                      ]
                                                                    )
                                                                  )
                                                                )
                                                              ]
                                                              (delay
                                                                (force
                                                                  [
                                                                    [
                                                                      [
                                                                        {
                                                                          [
                                                                            {
                                                                              Extended_match
                                                                              a
                                                                            }
                                                                            ds
                                                                          ]
                                                                          (delayed Ordering)
                                                                        }
                                                                        (lam
                                                                          l
                                                                          a
                                                                          (delay
                                                                            (force
                                                                              [
                                                                                [
                                                                                  [
                                                                                    {
                                                                                      [
                                                                                        {
                                                                                          Extended_match
                                                                                          a
                                                                                        }
                                                                                        ds
                                                                                      ]
                                                                                      (delayed Ordering)
                                                                                    }
                                                                                    (lam
                                                                                      r
                                                                                      a
                                                                                      (delay
                                                                                        [
                                                                                          [
                                                                                            [
                                                                                              {
                                                                                                compare
                                                                                                a
                                                                                              }
                                                                                              dOrd
                                                                                            ]
                                                                                            l
                                                                                          ]
                                                                                          r
                                                                                        ]
                                                                                      )
                                                                                    )
                                                                                  ]
                                                                                  (delay
                                                                                    [
                                                                                      fail
                                                                                      (abs
                                                                                        e
                                                                                        (type)
                                                                                        (error
                                                                                          e
                                                                                        )
                                                                                      )
                                                                                    ]
                                                                                  )
                                                                                ]
                                                                                (delay
                                                                                  [
                                                                                    fail
                                                                                    (abs
                                                                                      e
                                                                                      (type)
                                                                                      (error
                                                                                        e
                                                                                      )
                                                                                    )
                                                                                  ]
                                                                                )
                                                                              ]
                                                                            )
                                                                          )
                                                                        )
                                                                      ]
                                                                      (delay
                                                                        [
                                                                          fail
                                                                          (abs
                                                                            e
                                                                            (type)
                                                                            (error
                                                                              e
                                                                            )
                                                                          )
                                                                        ]
                                                                      )
                                                                    ]
                                                                    (delay GT)
                                                                  ]
                                                                )
                                                              )
                                                            ]
                                                            (delay LT)
                                                          ]
                                                        )
                                                      )
                                                    )
                                                    (delay
                                                      (force
                                                        [
                                                          [
                                                            [
                                                              {
                                                                [
                                                                  {
                                                                    Extended_match
                                                                    a
                                                                  }
                                                                  ds
                                                                ]
                                                                (delayed Ordering)
                                                              }
                                                              (lam
                                                                default_arg0
                                                                a
                                                                (delay
                                                                  [
                                                                    fail
                                                                    (abs
                                                                      e
                                                                      (type)
                                                                      (error e)
                                                                    )
                                                                  ]
                                                                )
                                                              )
                                                            ]
                                                            (delay
                                                              [
                                                                fail
                                                                (abs
                                                                  e
                                                                  (type)
                                                                  (error e)
                                                                )
                                                              ]
                                                            )
                                                          ]
                                                          (delay
                                                            (force
                                                              [
                                                                [
                                                                  [
                                                                    {
                                                                      [
                                                                        {
                                                                          Extended_match
                                                                          a
                                                                        }
                                                                        ds
                                                                      ]
                                                                      (delayed Ordering)
                                                                    }
                                                                    (lam
                                                                      default_arg0
                                                                      a
                                                                      (delay
                                                                        [
                                                                          fail
                                                                          (abs
                                                                            e
                                                                            (type)
                                                                            (error
                                                                              e
                                                                            )
                                                                          )
                                                                        ]
                                                                      )
                                                                    )
                                                                  ]
                                                                  (delay
                                                                    [
                                                                      fail
                                                                      (abs
                                                                        e
                                                                        (type)
                                                                        (error e
                                                                        )
                                                                      )
                                                                    ]
                                                                  )
                                                                ]
                                                                (delay EQ)
                                                              ]
                                                            )
                                                          )
                                                        ]
                                                      )
                                                    )
                                                  )
                                                )
                                              ]
                                              (delay GT)
                                            ]
                                            (delay
                                              (force
                                                [
                                                  [
                                                    [
                                                      {
                                                        [
                                                          { Extended_match a }
                                                          ds
                                                        ]
                                                        (delayed Ordering)
                                                      }
                                                      (lam
                                                        default_arg0
                                                        a
                                                        (delay
                                                          [
                                                            fail
                                                            (abs
                                                              e (type) (error e)
                                                            )
                                                          ]
                                                        )
                                                      )
                                                    ]
                                                    (delay
                                                      [
                                                        fail
                                                        (abs e (type) (error e))
                                                      ]
                                                    )
                                                  ]
                                                  (delay
                                                    (force
                                                      [
                                                        [
                                                          [
                                                            {
                                                              [
                                                                {
                                                                  Extended_match
                                                                  a
                                                                }
                                                                ds
                                                              ]
                                                              (delayed Ordering)
                                                            }
                                                            (lam
                                                              default_arg0
                                                              a
                                                              (delay
                                                                [
                                                                  fail
                                                                  (abs
                                                                    e
                                                                    (type)
                                                                    (error e)
                                                                  )
                                                                ]
                                                              )
                                                            )
                                                          ]
                                                          (delay
                                                            [
                                                              fail
                                                              (abs
                                                                e
                                                                (type)
                                                                (error e)
                                                              )
                                                            ]
                                                          )
                                                        ]
                                                        (delay EQ)
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
                            )
                          )
                        )
                      )
                      (termbind
                        (strict)
                        (vardecl
                          fOrdUpperBound0_c
                          (all a (type) (fun [Ord a] (fun [UpperBound a] (fun [UpperBound a] Bool))))
                        )
                        (abs
                          a
                          (type)
                          (lam
                            dOrd
                            [Ord a]
                            (lam
                              x
                              [UpperBound a]
                              (lam
                                y
                                [UpperBound a]
                                [
                                  { [ { UpperBound_match a } x ] Bool }
                                  (lam
                                    v
                                    [Extended a]
                                    (lam
                                      in
                                      Bool
                                      [
                                        { [ { UpperBound_match a } y ] Bool }
                                        (lam
                                          v
                                          [Extended a]
                                          (lam
                                            in
                                            Bool
                                            (force
                                              [
                                                [
                                                  [
                                                    {
                                                      [
                                                        Ordering_match
                                                        [
                                                          [
                                                            [
                                                              {
                                                                hull_ccompare a
                                                              }
                                                              dOrd
                                                            ]
                                                            v
                                                          ]
                                                          v
                                                        ]
                                                      ]
                                                      (delayed Bool)
                                                    }
                                                    (delay
                                                      (force
                                                        [
                                                          [
                                                            {
                                                              [ Bool_match in ]
                                                              (delayed Bool)
                                                            }
                                                            (delay in)
                                                          ]
                                                          (delay True)
                                                        ]
                                                      )
                                                    )
                                                  ]
                                                  (delay False)
                                                ]
                                                (delay True)
                                              ]
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
                        )
                      )
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
                            dOrd
                            [Ord a]
                            (lam
                              ds
                              [Interval a]
                              (lam
                                ds
                                [Interval a]
                                [
                                  { [ { Interval_match a } ds ] Bool }
                                  (lam
                                    l
                                    [LowerBound a]
                                    (lam
                                      h
                                      [UpperBound a]
                                      [
                                        { [ { Interval_match a } ds ] Bool }
                                        (lam
                                          l
                                          [LowerBound a]
                                          (lam
                                            h
                                            [UpperBound a]
                                            [
                                              {
                                                [ { LowerBound_match a } l ]
                                                Bool
                                              }
                                              (lam
                                                v
                                                [Extended a]
                                                (lam
                                                  in
                                                  Bool
                                                  [
                                                    {
                                                      [
                                                        { LowerBound_match a } l
                                                      ]
                                                      Bool
                                                    }
                                                    (lam
                                                      v
                                                      [Extended a]
                                                      (lam
                                                        in
                                                        Bool
                                                        (force
                                                          [
                                                            [
                                                              [
                                                                {
                                                                  [
                                                                    Ordering_match
                                                                    [
                                                                      [
                                                                        [
                                                                          {
                                                                            hull_ccompare
                                                                            a
                                                                          }
                                                                          dOrd
                                                                        ]
                                                                        v
                                                                      ]
                                                                      v
                                                                    ]
                                                                  ]
                                                                  (delayed Bool)
                                                                }
                                                                (delay
                                                                  (force
                                                                    [
                                                                      [
                                                                        {
                                                                          [
                                                                            Bool_match
                                                                            in
                                                                          ]
                                                                          (delayed Bool)
                                                                        }
                                                                        (delay
                                                                          (force
                                                                            [
                                                                              [
                                                                                {
                                                                                  [
                                                                                    Bool_match
                                                                                    in
                                                                                  ]
                                                                                  (delayed Bool)
                                                                                }
                                                                                (delay
                                                                                  [
                                                                                    [
                                                                                      [
                                                                                        {
                                                                                          fOrdUpperBound0_c
                                                                                          a
                                                                                        }
                                                                                        dOrd
                                                                                      ]
                                                                                      h
                                                                                    ]
                                                                                    h
                                                                                  ]
                                                                                )
                                                                              ]
                                                                              (delay
                                                                                False
                                                                              )
                                                                            ]
                                                                          )
                                                                        )
                                                                      ]
                                                                      (delay
                                                                        [
                                                                          [
                                                                            [
                                                                              {
                                                                                fOrdUpperBound0_c
                                                                                a
                                                                              }
                                                                              dOrd
                                                                            ]
                                                                            h
                                                                          ]
                                                                          h
                                                                        ]
                                                                      )
                                                                    ]
                                                                  )
                                                                )
                                                              ]
                                                              (delay False)
                                                            ]
                                                            (delay
                                                              [
                                                                [
                                                                  [
                                                                    {
                                                                      fOrdUpperBound0_c
                                                                      a
                                                                    }
                                                                    dOrd
                                                                  ]
                                                                  h
                                                                ]
                                                                h
                                                              ]
                                                            )
                                                          ]
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
                          wremainingFrom
                          (fun (con integer) (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun [Interval (con integer)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]])))
                        )
                        (lam
                          ww
                          (con integer)
                          (lam
                            ww
                            [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                            (lam
                              w
                              [Interval (con integer)]
                              [
                                [ [ unionWith addInteger ] ww ]
                                [
                                  [
                                    fAdditiveGroupValue_cscale (con integer -1)
                                  ]
                                  (force
                                    [
                                      [
                                        {
                                          [
                                            Bool_match
                                            [
                                              [
                                                [
                                                  { contains (con integer) }
                                                  fOrdPOSIXTime
                                                ]
                                                [
                                                  [
                                                    { Interval (con integer) }
                                                    [
                                                      [
                                                        {
                                                          LowerBound
                                                          (con integer)
                                                        }
                                                        [
                                                          {
                                                            Finite (con integer)
                                                          }
                                                          ww
                                                        ]
                                                      ]
                                                      True
                                                    ]
                                                  ]
                                                  [
                                                    [
                                                      {
                                                        UpperBound (con integer)
                                                      }
                                                      { PosInf (con integer) }
                                                    ]
                                                    True
                                                  ]
                                                ]
                                              ]
                                              w
                                            ]
                                          ]
                                          (delayed [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]])
                                        }
                                        (delay ww)
                                      ]
                                      (delay
                                        {
                                          Nil
                                          [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                        }
                                      )
                                    ]
                                  )
                                ]
                              ]
                            )
                          )
                        )
                      )
                      (termbind
                        (strict)
                        (vardecl
                          remainingFrom
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
                                [ VestingTranche_match w ]
                                [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                              }
                              (lam
                                ww
                                (con integer)
                                (lam
                                  ww
                                  [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                  [ [ [ wremainingFrom ww ] ww ] w ]
                                )
                              )
                            ]
                          )
                        )
                      )
                      (termbind
                        (strict)
                        (vardecl
                          scriptOutputsAt
                          (fun (con bytestring) (fun TxInfo [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]]))
                        )
                        (lam
                          h
                          (con bytestring)
                          (lam
                            p
                            TxInfo
                            [
                              {
                                [ TxInfo_match p ]
                                [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]]
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
                                        [List DCert]
                                        (lam
                                          ds
                                          [List [[Tuple2 StakingCredential] (con integer)]]
                                          (lam
                                            ds
                                            [Interval (con integer)]
                                            (lam
                                              ds
                                              [List (con bytestring)]
                                              (lam
                                                ds
                                                [List [[Tuple2 (con bytestring)] (con data)]]
                                                (lam
                                                  ds
                                                  (con bytestring)
                                                  [
                                                    [
                                                      [
                                                        {
                                                          { foldr TxOut }
                                                          [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]]
                                                        }
                                                        (lam
                                                          e
                                                          TxOut
                                                          (lam
                                                            xs
                                                            [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]]
                                                            [
                                                              {
                                                                [
                                                                  TxOut_match e
                                                                ]
                                                                [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]]
                                                              }
                                                              (lam
                                                                ds
                                                                Address
                                                                (lam
                                                                  ds
                                                                  [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]
                                                                  (lam
                                                                    ds
                                                                    [Maybe (con bytestring)]
                                                                    (force
                                                                      [
                                                                        [
                                                                          {
                                                                            [
                                                                              {
                                                                                Maybe_match
                                                                                (con bytestring)
                                                                              }
                                                                              ds
                                                                            ]
                                                                            (delayed [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]])
                                                                          }
                                                                          (lam
                                                                            ds
                                                                            (con bytestring)
                                                                            (delay
                                                                              [
                                                                                {
                                                                                  [
                                                                                    Address_match
                                                                                    ds
                                                                                  ]
                                                                                  [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]]
                                                                                }
                                                                                (lam
                                                                                  ds
                                                                                  Credential
                                                                                  (lam
                                                                                    ds
                                                                                    [Maybe StakingCredential]
                                                                                    [
                                                                                      [
                                                                                        {
                                                                                          [
                                                                                            Credential_match
                                                                                            ds
                                                                                          ]
                                                                                          [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]]
                                                                                        }
                                                                                        (lam
                                                                                          ipv
                                                                                          (con bytestring)
                                                                                          xs
                                                                                        )
                                                                                      ]
                                                                                      (lam
                                                                                        s
                                                                                        (con bytestring)
                                                                                        (force
                                                                                          [
                                                                                            [
                                                                                              {
                                                                                                [
                                                                                                  Bool_match
                                                                                                  [
                                                                                                    [
                                                                                                      [
                                                                                                        {
                                                                                                          (builtin
                                                                                                            ifThenElse
                                                                                                          )
                                                                                                          Bool
                                                                                                        }
                                                                                                        [
                                                                                                          [
                                                                                                            (builtin
                                                                                                              equalsByteString
                                                                                                            )
                                                                                                            s
                                                                                                          ]
                                                                                                          h
                                                                                                        ]
                                                                                                      ]
                                                                                                      True
                                                                                                    ]
                                                                                                    False
                                                                                                  ]
                                                                                                ]
                                                                                                (delayed [List [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]])
                                                                                              }
                                                                                              (delay
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
                                                                                            (delay
                                                                                              xs
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
                                                                        (delay
                                                                          xs
                                                                        )
                                                                      ]
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
                                                        [[Tuple2 (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]]]
                                                      }
                                                    ]
                                                    ds
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
                                { [ { { Tuple2_match a } b } ds ] b }
                                (lam ds a (lam b b b))
                              ]
                            )
                          )
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
                                        [List DCert]
                                        (lam
                                          ds
                                          [List [[Tuple2 StakingCredential] (con integer)]]
                                          (lam
                                            ds
                                            [Interval (con integer)]
                                            (lam
                                              ds
                                              [List (con bytestring)]
                                              (lam
                                                ds
                                                [List [[Tuple2 (con bytestring)] (con data)]]
                                                (lam
                                                  ds
                                                  (con bytestring)
                                                  (force
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
                                                                  (force
                                                                    [
                                                                      [
                                                                        {
                                                                          [
                                                                            Bool_match
                                                                            [
                                                                              [
                                                                                [
                                                                                  {
                                                                                    (builtin
                                                                                      ifThenElse
                                                                                    )
                                                                                    Bool
                                                                                  }
                                                                                  [
                                                                                    [
                                                                                      (builtin
                                                                                        equalsByteString
                                                                                      )
                                                                                      k
                                                                                    ]
                                                                                    x
                                                                                  ]
                                                                                ]
                                                                                True
                                                                              ]
                                                                              False
                                                                            ]
                                                                          ]
                                                                          (delayed [Maybe (con bytestring)])
                                                                        }
                                                                        (delay
                                                                          [
                                                                            {
                                                                              Just
                                                                              (con bytestring)
                                                                            }
                                                                            x
                                                                          ]
                                                                        )
                                                                      ]
                                                                      (delay
                                                                        {
                                                                          Nothing
                                                                          (con bytestring)
                                                                        }
                                                                      )
                                                                    ]
                                                                  )
                                                                )
                                                              ]
                                                              ds
                                                            ]
                                                          ]
                                                          (delayed Bool)
                                                        }
                                                        (lam
                                                          ds
                                                          (con bytestring)
                                                          (delay True)
                                                        )
                                                      ]
                                                      (delay False)
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
                              )
                            ]
                          )
                        )
                      )
                      (termbind
                        (strict)
                        (vardecl
                          validate
                          (fun VestingParams (fun Unit (fun Unit (fun ScriptContext Bool))))
                        )
                        (lam
                          ds
                          VestingParams
                          (lam
                            ds
                            Unit
                            (lam
                              ds
                              Unit
                              (lam
                                ctx
                                ScriptContext
                                [
                                  { [ VestingParams_match ds ] Bool }
                                  (lam
                                    ds
                                    VestingTranche
                                    (lam
                                      ds
                                      VestingTranche
                                      (lam
                                        ds
                                        (con bytestring)
                                        [
                                          { [ Unit_match ds ] Bool }
                                          [
                                            { [ Unit_match ds ] Bool }
                                            [
                                              {
                                                [ ScriptContext_match ctx ] Bool
                                              }
                                              (lam
                                                ds
                                                TxInfo
                                                (lam
                                                  ds
                                                  ScriptPurpose
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
                                                              [List DCert]
                                                              (lam
                                                                ds
                                                                [List [[Tuple2 StakingCredential] (con integer)]]
                                                                (lam
                                                                  ds
                                                                  [Interval (con integer)]
                                                                  (lam
                                                                    ds
                                                                    [List (con bytestring)]
                                                                    (lam
                                                                      ds
                                                                      [List [[Tuple2 (con bytestring)] (con data)]]
                                                                      (lam
                                                                        ds
                                                                        (con bytestring)
                                                                        (force
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
                                                                                              scriptOutputsAt
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
                                                                                                      ownHashes
                                                                                                      ctx
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
                                                                                            remainingFrom
                                                                                            ds
                                                                                          ]
                                                                                          ds
                                                                                        ]
                                                                                      ]
                                                                                      [
                                                                                        [
                                                                                          remainingFrom
                                                                                          ds
                                                                                        ]
                                                                                        ds
                                                                                      ]
                                                                                    ]
                                                                                  ]
                                                                                ]
                                                                                (delayed Bool)
                                                                              }
                                                                              (delay
                                                                                [
                                                                                  [
                                                                                    txSignedBy
                                                                                    ds
                                                                                  ]
                                                                                  ds
                                                                                ]
                                                                              )
                                                                            ]
                                                                            (delay
                                                                              False
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
                                                        )
                                                      )
                                                    )
                                                  ]
                                                )
                                              )
                                            ]
                                          ]
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