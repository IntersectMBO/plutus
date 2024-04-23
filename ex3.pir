(program
  1.1.0
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
      (nonstrict)
      (vardecl not (fun Bool Bool))
      (lam
        a
        Bool
        {
          [
            [
              { [ Bool_match a ] (all dead (type) Bool) }
              (abs dead (type) False)
            ]
            (abs dead (type) True)
          ]
          (all dead (type) dead)
        }
      )
    )
    (lam x Bool (let (nonrec) (termbind (strict) (vardecl x Bool) x) [ not x ]))
  )
)