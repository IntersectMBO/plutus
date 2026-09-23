-- Reject a token ID that is too long.
(program 1.0.0
  (con value
    [ (#,
        [ (#, 456)
        , (#aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 123)
        ]
      )
    ]
  )
)
