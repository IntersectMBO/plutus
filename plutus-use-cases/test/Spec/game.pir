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
              (vardecl sha2_ (fun (con bytestring) (con bytestring)))
              (builtin sha2_256)
            )
            (let
              (nonrec)
              (datatypebind
                (datatype
                  (tyvardecl ClearString (type))
                  
                  ClearString_match
                  (vardecl ClearString (fun (con bytestring) ClearString))
                )
              )
              (let
                (nonrec)
                (datatypebind
                  (datatype
                    (tyvardecl HashedString (type))
                    
                    HashedString_match
                    (vardecl HashedString (fun (con bytestring) HashedString))
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
                          Interval (fun [Maybe a] (fun [Maybe a] [Interval a]))
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
                              (tyvardecl PendingTxOutType (type))
                              
                              PendingTxOutType_match
                              (vardecl DataTxOut PendingTxOutType)
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
                                (tyvardecl PendingTxOut (type))
                                
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
                                    validateGuess
                                    (fun HashedString (fun ClearString (fun PendingTx Bool)))
                                  )
                                  (lam
                                    dataScript
                                    HashedString
                                    (lam
                                      redeemerScript
                                      ClearString
                                      (lam
                                        ds
                                        PendingTx
                                        [
                                          {
                                            [ HashedString_match dataScript ]
                                            Bool
                                          }
                                          (lam
                                            actual
                                            (con bytestring)
                                            [
                                              {
                                                [
                                                  ClearString_match
                                                  redeemerScript
                                                ]
                                                Bool
                                              }
                                              (lam
                                                guess
                                                (con bytestring)
                                                [
                                                  [ equalsByteString actual ]
                                                  [ sha2_ guess ]
                                                ]
                                              )
                                            ]
                                          )
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