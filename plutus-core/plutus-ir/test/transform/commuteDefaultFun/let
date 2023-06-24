-- the constant 5 should turn into the first argument of ((==) (10+2)) 5)
-- this tests that it works in the subterms. 

(let
  (nonrec)

  (termbind
    (strict)
    (vardecl x (con integer))
    (error (con integer))
  )

  [
    [ (builtin equalsInteger)  
        [
            [(builtin addInteger) (con integer 10)] x
        ]
    ] (con integer 5)
  ]
)
