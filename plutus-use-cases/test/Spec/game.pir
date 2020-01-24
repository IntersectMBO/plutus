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
                        UpperBound (fun [Extended a] (fun Bool [UpperBound a]))
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
                                        sha2_
                                        (fun (con bytestring) (con bytestring))
                                      )
                                      (builtin sha2_256)
                                    )
                                    (let
                                      (nonrec)
                                      (termbind
                                        (strict)
                                        (vardecl
                                          validateGuess
                                          (fun (con bytestring) (fun (con bytestring) (fun [PendingTx [PendingTxIn [[[Tuple3 (con bytestring)] (con bytestring)] (con bytestring)]]] Bool)))
                                        )
                                        (lam
                                          ds
                                          (con bytestring)
                                          (lam
                                            ds
                                            (con bytestring)
                                            (lam
                                              ds
                                              [PendingTx [PendingTxIn [[[Tuple3 (con bytestring)] (con bytestring)] (con bytestring)]]]
                                              [
                                                [ equalsByteString ds ]
                                                [ sha2_ ds ]
                                              ]
                                            )
                                          )
                                        )
                                      )
                                      validateGuess
                                    )
                                  )
                                )
                              )
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
  )
)