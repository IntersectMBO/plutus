-- Data.Constr checks both its Word64 tag and exact field arity before exposing fields.
(program 1.2.0
  (match (con data (Constr 18446744073709551615 [I 1, I 2, I 3]))
    (pattern (data-constr 18446744073709551614) (error))
    (pattern
      (data-constr 18446744073709551615 (wildcard) (wildcard))
      (error))
    (pattern
      (data-constr 18446744073709551615 (wildcard) (bind) (wildcard))
      (lam middle middle))
    (pattern (wildcard) (error)))
)
