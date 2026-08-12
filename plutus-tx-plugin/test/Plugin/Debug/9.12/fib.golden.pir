(program
  { no-src-span }
  1.1.0
  (let
    { no-src-span }
    (nonrec)
    (termbind
      { no-src-span }
      (strict)
      (vardecl
        { no-src-span }
        addInteger
        (fun
          { no-src-span }
          (con { no-src-span } integer)
          (fun
            { no-src-span }
            (con { no-src-span } integer)
            (con { no-src-span } integer)
          )
        )
      )
      (builtin { no-src-span } addInteger)
    )
    (termbind
      { no-src-span }
      (nonstrict)
      (vardecl
        { no-src-span }
        addInteger
        (fun
          { no-src-span }
          (con { no-src-span } integer)
          (fun
            { no-src-span }
            (con { no-src-span } integer)
            (con { no-src-span } integer)
          )
        )
      )
      (lam
        { no-src-span }
        x
        (con { no-src-span } integer)
        (let
          { no-src-span }
          (nonrec)
          (termbind
            { no-src-span }
            (strict)
            (vardecl { no-src-span } x (con { no-src-span } integer))
            { no-src-span } x
          )
          (lam
            { no-src-span }
            y
            (con { no-src-span } integer)
            (let
              { no-src-span }
              (nonrec)
              (termbind
                { no-src-span }
                (strict)
                (vardecl { no-src-span } y (con { no-src-span } integer))
                { no-src-span } y
              )
              [
                { no-src-span }
                [ { no-src-span } { no-src-span } addInteger { no-src-span } x ]
                { no-src-span } y
              ]
            )
          )
        )
      )
    )
    (termbind
      { no-src-span }
      (strict)
      (vardecl
        { no-src-span }
        equalsInteger
        (fun
          { no-src-span }
          (con { no-src-span } integer)
          (fun
            { no-src-span }
            (con { no-src-span } integer)
            (con { no-src-span } bool)
          )
        )
      )
      (builtin { no-src-span } equalsInteger)
    )
    (termbind
      { no-src-span }
      (nonstrict)
      (vardecl
        { no-src-span }
        equalsInteger
        (fun
          { no-src-span }
          (con { no-src-span } integer)
          (fun
            { no-src-span }
            (con { no-src-span } integer)
            (con { no-src-span } bool)
          )
        )
      )
      (lam
        { no-src-span }
        x
        (con { no-src-span } integer)
        (let
          { no-src-span }
          (nonrec)
          (termbind
            { no-src-span }
            (strict)
            (vardecl { no-src-span } x (con { no-src-span } integer))
            { no-src-span } x
          )
          (lam
            { no-src-span }
            y
            (con { no-src-span } integer)
            (let
              { no-src-span }
              (nonrec)
              (termbind
                { no-src-span }
                (strict)
                (vardecl { no-src-span } y (con { no-src-span } integer))
                { no-src-span } y
              )
              [
                { no-src-span }
                [
                  { no-src-span }
                  { no-src-span } equalsInteger
                  { no-src-span } x
                ]
                { no-src-span } y
              ]
            )
          )
        )
      )
    )
    (termbind
      { no-src-span }
      (strict)
      (vardecl
        { no-src-span }
        subtractInteger
        (fun
          { no-src-span }
          (con { no-src-span } integer)
          (fun
            { no-src-span }
            (con { no-src-span } integer)
            (con { no-src-span } integer)
          )
        )
      )
      (builtin { no-src-span } subtractInteger)
    )
    (termbind
      { no-src-span }
      (nonstrict)
      (vardecl
        { no-src-span }
        subtractInteger
        (fun
          { no-src-span }
          (con { no-src-span } integer)
          (fun
            { no-src-span }
            (con { no-src-span } integer)
            (con { no-src-span } integer)
          )
        )
      )
      (lam
        { no-src-span }
        x
        (con { no-src-span } integer)
        (let
          { no-src-span }
          (nonrec)
          (termbind
            { no-src-span }
            (strict)
            (vardecl { no-src-span } x (con { no-src-span } integer))
            { no-src-span } x
          )
          (lam
            { no-src-span }
            y
            (con { no-src-span } integer)
            (let
              { no-src-span }
              (nonrec)
              (termbind
                { no-src-span }
                (strict)
                (vardecl { no-src-span } y (con { no-src-span } integer))
                { no-src-span } y
              )
              [
                { no-src-span }
                [
                  { no-src-span }
                  { no-src-span } subtractInteger
                  { no-src-span } x
                ]
                { no-src-span } y
              ]
            )
          )
        )
      )
    )
    (let
      { no-src-span }
      (rec)
      (termbind
        { no-src-span }
        (nonstrict)
        (vardecl
          { no-src-span }
          fib
          (fun
            { no-src-span }
            (con { no-src-span } integer)
            (con { no-src-span } integer)
          )
        )
        (lam
          { no-src-span }
          n
          (con { no-src-span } integer)
          (let
            { test/Plugin/Debug/Spec.hs:43:11-52:58 }
            (nonrec)
            (termbind
              { test/Plugin/Debug/Spec.hs:43:11-52:58 }
              (strict)
              (vardecl
                { test/Plugin/Debug/Spec.hs:43:11-52:58 }
                n
                (con { test/Plugin/Debug/Spec.hs:43:11-52:58 } integer)
              )
              { test/Plugin/Debug/Spec.hs:43:11-52:58 } n
            )
            {
              { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58 }
              (case
                { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58 }
                (all
                  { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58 }
                  dead
                  ({ test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58 }
                  type)
                  (con
                    { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58 }
                    integer
                  )
                )
                [
                  { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58 }
                  [
                    { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58 }
                    { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58 }
                    equalsInteger
                    { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58, test/Plugin/Debug/Spec.hs:44:39-44:39 }
                    n
                  ]
                  (con
                    { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58, test/Plugin/Debug/Spec.hs:44:41-44:41 }
                    integer
                    0
                  )
                ]
                (abs
                  { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58 }
                  dead
                  ({ test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58 }
                  type)
                  {
                    { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58, test/Plugin/Debug/Spec.hs:47:17-52:58 }
                    (case
                      { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58, test/Plugin/Debug/Spec.hs:47:17-52:58 }
                      (all
                        { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58, test/Plugin/Debug/Spec.hs:47:17-52:58 }
                        dead
                        ({ test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58, test/Plugin/Debug/Spec.hs:47:17-52:58 }
                        type)
                        (con
                          { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58, test/Plugin/Debug/Spec.hs:47:17-52:58 }
                          integer
                        )
                      )
                      [
                        { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58, test/Plugin/Debug/Spec.hs:47:17-52:58 }
                        [
                          { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58, test/Plugin/Debug/Spec.hs:47:17-52:58 }
                          { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58, test/Plugin/Debug/Spec.hs:47:17-52:58 }
                          equalsInteger
                          { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58, test/Plugin/Debug/Spec.hs:47:17-52:58, test/Plugin/Debug/Spec.hs:47:43-47:43 }
                          n
                        ]
                        (con
                          { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58, test/Plugin/Debug/Spec.hs:47:17-52:58, test/Plugin/Debug/Spec.hs:47:45-47:45 }
                          integer
                          1
                        )
                      ]
                      (abs
                        { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58, test/Plugin/Debug/Spec.hs:47:17-52:58 }
                        dead
                        ({ test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58, test/Plugin/Debug/Spec.hs:47:17-52:58 }
                        type)
                        [
                          { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58, test/Plugin/Debug/Spec.hs:47:17-52:58, test/Plugin/Debug/Spec.hs:50:21-52:58 }
                          [
                            { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58, test/Plugin/Debug/Spec.hs:47:17-52:58, test/Plugin/Debug/Spec.hs:50:21-52:58 }
                            { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58, test/Plugin/Debug/Spec.hs:47:17-52:58, test/Plugin/Debug/Spec.hs:50:21-52:58 }
                            addInteger
                            [
                              { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58, test/Plugin/Debug/Spec.hs:47:17-52:58, test/Plugin/Debug/Spec.hs:50:21-52:58, test/Plugin/Debug/Spec.hs:51:23-51:58 }
                              { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58, test/Plugin/Debug/Spec.hs:47:17-52:58, test/Plugin/Debug/Spec.hs:50:21-52:58, test/Plugin/Debug/Spec.hs:51:23-51:58 }
                              fib
                              [
                                { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58, test/Plugin/Debug/Spec.hs:47:17-52:58, test/Plugin/Debug/Spec.hs:50:21-52:58, test/Plugin/Debug/Spec.hs:51:23-51:58, test/Plugin/Debug/Spec.hs:51:28-51:57 }
                                [
                                  { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58, test/Plugin/Debug/Spec.hs:47:17-52:58, test/Plugin/Debug/Spec.hs:50:21-52:58, test/Plugin/Debug/Spec.hs:51:23-51:58, test/Plugin/Debug/Spec.hs:51:28-51:57 }
                                  { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58, test/Plugin/Debug/Spec.hs:47:17-52:58, test/Plugin/Debug/Spec.hs:50:21-52:58, test/Plugin/Debug/Spec.hs:51:23-51:58, test/Plugin/Debug/Spec.hs:51:28-51:57 }
                                  subtractInteger
                                  { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58, test/Plugin/Debug/Spec.hs:47:17-52:58, test/Plugin/Debug/Spec.hs:50:21-52:58, test/Plugin/Debug/Spec.hs:51:23-51:58, test/Plugin/Debug/Spec.hs:51:28-51:57, test/Plugin/Debug/Spec.hs:51:54-51:54 }
                                  n
                                ]
                                (con
                                  { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58, test/Plugin/Debug/Spec.hs:47:17-52:58, test/Plugin/Debug/Spec.hs:50:21-52:58, test/Plugin/Debug/Spec.hs:51:23-51:58, test/Plugin/Debug/Spec.hs:51:28-51:57, test/Plugin/Debug/Spec.hs:51:56-51:56 }
                                  integer
                                  1
                                )
                              ]
                            ]
                          ]
                          [
                            { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58, test/Plugin/Debug/Spec.hs:47:17-52:58, test/Plugin/Debug/Spec.hs:50:21-52:58, test/Plugin/Debug/Spec.hs:52:23-52:58 }
                            { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58, test/Plugin/Debug/Spec.hs:47:17-52:58, test/Plugin/Debug/Spec.hs:50:21-52:58, test/Plugin/Debug/Spec.hs:52:23-52:58 }
                            fib
                            [
                              { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58, test/Plugin/Debug/Spec.hs:47:17-52:58, test/Plugin/Debug/Spec.hs:50:21-52:58, test/Plugin/Debug/Spec.hs:52:23-52:58, test/Plugin/Debug/Spec.hs:52:28-52:57 }
                              [
                                { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58, test/Plugin/Debug/Spec.hs:47:17-52:58, test/Plugin/Debug/Spec.hs:50:21-52:58, test/Plugin/Debug/Spec.hs:52:23-52:58, test/Plugin/Debug/Spec.hs:52:28-52:57 }
                                { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58, test/Plugin/Debug/Spec.hs:47:17-52:58, test/Plugin/Debug/Spec.hs:50:21-52:58, test/Plugin/Debug/Spec.hs:52:23-52:58, test/Plugin/Debug/Spec.hs:52:28-52:57 }
                                subtractInteger
                                { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58, test/Plugin/Debug/Spec.hs:47:17-52:58, test/Plugin/Debug/Spec.hs:50:21-52:58, test/Plugin/Debug/Spec.hs:52:23-52:58, test/Plugin/Debug/Spec.hs:52:28-52:57, test/Plugin/Debug/Spec.hs:52:54-52:54 }
                                n
                              ]
                              (con
                                { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58, test/Plugin/Debug/Spec.hs:47:17-52:58, test/Plugin/Debug/Spec.hs:50:21-52:58, test/Plugin/Debug/Spec.hs:52:23-52:58, test/Plugin/Debug/Spec.hs:52:28-52:57, test/Plugin/Debug/Spec.hs:52:56-52:56 }
                                integer
                                2
                              )
                            ]
                          ]
                        ]
                      )
                      (abs
                        { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58, test/Plugin/Debug/Spec.hs:47:17-52:58 }
                        dead
                        ({ test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58, test/Plugin/Debug/Spec.hs:47:17-52:58 }
                        type)
                        (con
                          { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58, test/Plugin/Debug/Spec.hs:47:17-52:58, test/Plugin/Debug/Spec.hs:48:24-48:24 }
                          integer
                          1
                        )
                      )
                    )
                    (all
                      { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58, test/Plugin/Debug/Spec.hs:47:17-52:58 }
                      dead
                      ({ test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58, test/Plugin/Debug/Spec.hs:47:17-52:58 }
                      type)
                      { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58, test/Plugin/Debug/Spec.hs:47:17-52:58 }
                      dead
                    )
                  }
                )
                (abs
                  { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58 }
                  dead
                  ({ test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58 }
                  type)
                  (con
                    { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58, test/Plugin/Debug/Spec.hs:45:20-45:20 }
                    integer
                    0
                  )
                )
              )
              (all
                { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58 }
                dead
                ({ test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58 }
                type)
                { test/Plugin/Debug/Spec.hs:43:11-52:58, test/Plugin/Debug/Spec.hs:44:13-52:58 }
                dead
              )
            }
          )
        )
      )
      { test/Plugin/Debug/Spec.hs:42:5-54:5 } fib
    )
  )
)