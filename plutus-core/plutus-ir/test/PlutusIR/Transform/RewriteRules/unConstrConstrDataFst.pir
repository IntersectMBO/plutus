-- this adds some traces to make sure that the effect order is preserved,
-- also the trace messages should not appear duplicated
(let
    (nonrec)
    (datatypebind
      (datatype
        (tyvardecl MyD_1099 (type))

        MyD_match_1102
        (vardecl MyD_1100 (fun (con integer) MyD_1099))
        (vardecl MyD_1101 (fun (con bytestring) MyD_1099))
      )
    )
         [{ { (builtin fstPair) (con integer) } [ (con list) (con data) ] }
          [
            (builtin unConstrData)
            [ (builtin constrData)
                  [{(builtin trace) (con integer)} (con string "BEFORE") (con integer 0)]
                  [{(builtin trace) [ (con list) (con data) ]}  (con string "AFTER")
                     [ { (builtin mkCons) (con data) } [ (builtin iData) (con integer 1) ]
                      [ (builtin mkNilData) (con unit ()) ]
                      ]
                      ]
            ]
          ]
         ]
)

