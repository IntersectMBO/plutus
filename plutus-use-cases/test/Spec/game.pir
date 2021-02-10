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
          (datatypebind
            (datatype
              (tyvardecl Bool (type))

              Bool_match
              (vardecl True Bool) (vardecl False Bool)
            )
          )
          (datatypebind
            (datatype
              (tyvardecl LowerBound (fun (type) (type)))
              (tyvardecl a (type))
              LowerBound_match
              (vardecl LowerBound (fun [Extended a] (fun Bool [LowerBound a])))
            )
          )
          (datatypebind
            (datatype
              (tyvardecl UpperBound (fun (type) (type)))
              (tyvardecl a (type))
              UpperBound_match
              (vardecl UpperBound (fun [Extended a] (fun Bool [UpperBound a])))
            )
          )
          (datatypebind
            (datatype
              (tyvardecl Interval (fun (type) (type)))
              (tyvardecl a (type))
              Interval_match
              (vardecl
                Interval (fun [LowerBound a] (fun [UpperBound a] [Interval a]))
              )
            )
          )
          (datatypebind
            (datatype
              (tyvardecl Tuple3 (fun (type) (fun (type) (fun (type) (type)))))
              (tyvardecl a (type)) (tyvardecl b (type)) (tyvardecl c (type))
              Tuple3_match
              (vardecl Tuple3 (fun a (fun b (fun c [[[Tuple3 a] b] c]))))
            )
          )
          (datatypebind
            (datatype
              (tyvardecl Maybe (fun (type) (type)))
              (tyvardecl a (type))
              Maybe_match
              (vardecl Just (fun a [Maybe a])) (vardecl Nothing [Maybe a])
            )
          )
          (datatypebind
            (datatype
              (tyvardecl TxOutRef (type))

              TxOutRef_match
              (vardecl
                TxOutRef (fun (con bytestring) (fun (con integer) TxOutRef))
              )
            )
          )
          (datatypebind
            (datatype
              (tyvardecl TxInInfo (type))

              TxInInfo_match
              (vardecl
                TxInInfo
                (fun TxOutRef (fun [Maybe [[[Tuple3 (con bytestring)] (con bytestring)] (con bytestring)]] (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] TxInInfo)))
              )
            )
          )
          (datatypebind
            (datatype
              (tyvardecl Address (type))

              Address_match
              (vardecl PubKeyAddress (fun (con bytestring) Address))
              (vardecl ScriptAddress (fun (con bytestring) Address))
            )
          )
          (datatypebind
            (datatype
              (tyvardecl TxOutType (type))

              TxOutType_match
              (vardecl PayToPubKey TxOutType)
              (vardecl PayToScript (fun (con bytestring) TxOutType))
            )
          )
          (datatypebind
            (datatype
              (tyvardecl TxOut (type))

              TxOut_match
              (vardecl
                TxOut
                (fun Address (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun TxOutType TxOut)))
              )
            )
          )
          (datatypebind
            (datatype
              (tyvardecl TxInfo (type))

              TxInfo_match
              (vardecl
                TxInfo
                (fun [List TxInInfo] (fun [List TxOut] (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] [[(lam k (type) (lam v (type) [List [[Tuple2 k] v]])) (con bytestring)] (con integer)]] (fun [Interval (con integer)] (fun [List (con bytestring)] (fun [List (con bytestring)] (fun [List [[Tuple2 (con bytestring)] Data]] (fun (con bytestring) TxInfo)))))))))
              )
            )
          )
          (datatypebind
            (datatype
              (tyvardecl ValidatorCtx (type))

              ValidatorCtx_match
              (vardecl
                ValidatorCtx (fun TxInfo (fun (con integer) ValidatorCtx))
              )
            )
          )
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
                    (con bool)
                    [ [ [ { (builtin ifThenElse) Bool } b ] True ] False ]
                  )
                  [ [ (builtin equalsByteString) arg ] arg ]
                ]
              )
            )
          )
          (termbind
            (strict)
            (vardecl
              validateGuess
              (fun (con bytestring) (fun (con bytestring) (fun ValidatorCtx Bool)))
            )
            (lam
              ds
              (con bytestring)
              (lam
                ds
                (con bytestring)
                (lam
                  ds
                  ValidatorCtx
                  [ [ equalsByteString ds ] [ (builtin sha2_256) ds ] ]
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