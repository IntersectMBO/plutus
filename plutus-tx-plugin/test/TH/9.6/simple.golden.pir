(lam
  ds
  (con bool)
  (let
    (nonrec)
    (termbind (strict) (vardecl ds (con bool)) ds)
    (case (con integer) ds (con integer 2) (con integer 1))
  )
)