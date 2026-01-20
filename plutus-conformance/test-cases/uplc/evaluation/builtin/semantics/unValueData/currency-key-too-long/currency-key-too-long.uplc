-- Currency symbol with 33 bytes (> maxKeyLen)
(program 1.0.0
  [
    (builtin unValueData)
    (con data
      (Map
        [ ( B #000000000000000000000000000000000000000000000000000000000000000000
          , Map [(B #, I 1)]
          )
        ]
      )
    )
  ]
)
