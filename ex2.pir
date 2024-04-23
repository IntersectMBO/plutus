(program
  1.1.0
  (let
    (nonrec)
    (typebind (tyvardecl Bool (type)) (all a (type) (fun a a)))
    (lam
      x
      Bool
      (let (nonrec) (termbind (strict) (vardecl x Bool) x) (lam y Bool x))
    )
  )
)