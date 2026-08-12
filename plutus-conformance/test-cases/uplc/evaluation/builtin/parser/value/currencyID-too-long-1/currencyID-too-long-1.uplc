-- Reject a currency ID that is too long.
(program 1.0.0
  (con value
    [ (#aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
        [ (#11, 123)
        , (#22, 456)
        ]
      )
    , (#bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb,
        [ (#0011, 12345)
        , (#0022, 45678)
        ]
      )
    ]
  )
)
