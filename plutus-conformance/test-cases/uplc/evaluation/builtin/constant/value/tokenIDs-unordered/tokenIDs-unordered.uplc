(program 1.0.0
  (con value
    [ (#123456, [ (#bb, 456)])
    , (#88,     [ (#88, 2), (#9999, 5), (#123456, 100)])
    -- Lexicograpically, #123456 precedes #88, so the currencies
    -- are in the correct order but the tokens aren't.
    , (#9999  , [ (#aa, 123)])
    ]
  )
)
