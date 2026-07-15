-- Reject a currency ID that is too long: note that the currencies are in the wrong order here.
(program 1.0.0
  (con value
    [ (#bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb,
        [ (#0011, 12345)
        , (#0022, 45678)
        ]
      )
    , (#aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
        [ (#11, 123)
        , (#22, 456)
        ]
      )
    ]
  )
)
