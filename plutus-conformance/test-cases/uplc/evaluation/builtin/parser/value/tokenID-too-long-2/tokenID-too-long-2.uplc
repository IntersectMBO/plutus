-- Reject a token ID that is too long: note that the tokens are in the wrong order here.
(program 1.0.0
  (con value
    [ (#,
        [ (#aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 123)
        , (#, 456)
        ]
      )
    ]
  )
)
