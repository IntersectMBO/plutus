-- Token name with 33 bytes (> maxKeyLen)
(program 1.0.0
  [
    (builtin unValueData)
    (con data
      (Map
        [ ( B #
          , Map [(B #000000000000000000000000000000000000000000000000000000000000000000, I 1)]
          )
        ]
      )
    )
  ]
)
