-- String has no scalar pattern of its own, but bind accepts every built-in constant.
(program 1.2.0
  (match (con string "opaque")
    (pattern (integer 0) (error))
    (pattern (bind) (lam captured captured)))
)
