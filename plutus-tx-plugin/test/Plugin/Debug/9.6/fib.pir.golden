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
            { test/Plugin/Debug/Spec.hs:48:11-57:58 }
            (nonrec)
            (termbind
              { test/Plugin/Debug/Spec.hs:48:11-57:58 }
              (strict)
              (vardecl
                { test/Plugin/Debug/Spec.hs:48:11-57:58 }
                n
                (con { test/Plugin/Debug/Spec.hs:48:11-57:58 } integer)
              )
              { test/Plugin/Debug/Spec.hs:48:11-57:58 } n
            )
            {
              { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58 }
              (case
                { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58 }
                (all
                  { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58 }
                  dead
                  ({ test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58 }
                  type)
                  (con
                    { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58 }
                    integer
                  )
                )
                [
                  { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58 }
                  [
                    { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58 }
                    { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58 }
                    equalsInteger
                    { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58, test/Plugin/Debug/Spec.hs:49:39-49:39 }
                    n
                  ]
                  (con
                    { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58, test/Plugin/Debug/Spec.hs:49:41-49:41 }
                    integer
                    0
                  )
                ]
                (abs
                  { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58 }
                  dead
                  ({ test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58 }
                  type)
                  {
                    { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58, test/Plugin/Debug/Spec.hs:52:17-57:58 }
                    (case
                      { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58, test/Plugin/Debug/Spec.hs:52:17-57:58 }
                      (all
                        { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58, test/Plugin/Debug/Spec.hs:52:17-57:58 }
                        dead
                        ({ test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58, test/Plugin/Debug/Spec.hs:52:17-57:58 }
                        type)
                        (con
                          { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58, test/Plugin/Debug/Spec.hs:52:17-57:58 }
                          integer
                        )
                      )
                      [
                        { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58, test/Plugin/Debug/Spec.hs:52:17-57:58 }
                        [
                          { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58, test/Plugin/Debug/Spec.hs:52:17-57:58 }
                          { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58, test/Plugin/Debug/Spec.hs:52:17-57:58 }
                          equalsInteger
                          { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58, test/Plugin/Debug/Spec.hs:52:17-57:58, test/Plugin/Debug/Spec.hs:52:43-52:43 }
                          n
                        ]
                        (con
                          { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58, test/Plugin/Debug/Spec.hs:52:17-57:58, test/Plugin/Debug/Spec.hs:52:45-52:45 }
                          integer
                          1
                        )
                      ]
                      (abs
                        { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58, test/Plugin/Debug/Spec.hs:52:17-57:58 }
                        dead
                        ({ test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58, test/Plugin/Debug/Spec.hs:52:17-57:58 }
                        type)
                        [
                          { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58, test/Plugin/Debug/Spec.hs:52:17-57:58, test/Plugin/Debug/Spec.hs:55:21-57:58 }
                          [
                            { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58, test/Plugin/Debug/Spec.hs:52:17-57:58, test/Plugin/Debug/Spec.hs:55:21-57:58 }
                            { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58, test/Plugin/Debug/Spec.hs:52:17-57:58, test/Plugin/Debug/Spec.hs:55:21-57:58 }
                            addInteger
                            [
                              { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58, test/Plugin/Debug/Spec.hs:52:17-57:58, test/Plugin/Debug/Spec.hs:55:21-57:58, test/Plugin/Debug/Spec.hs:56:23-56:58 }
                              { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58, test/Plugin/Debug/Spec.hs:52:17-57:58, test/Plugin/Debug/Spec.hs:55:21-57:58, test/Plugin/Debug/Spec.hs:56:23-56:58 }
                              fib
                              [
                                { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58, test/Plugin/Debug/Spec.hs:52:17-57:58, test/Plugin/Debug/Spec.hs:55:21-57:58, test/Plugin/Debug/Spec.hs:56:23-56:58, test/Plugin/Debug/Spec.hs:56:28-56:57 }
                                [
                                  { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58, test/Plugin/Debug/Spec.hs:52:17-57:58, test/Plugin/Debug/Spec.hs:55:21-57:58, test/Plugin/Debug/Spec.hs:56:23-56:58, test/Plugin/Debug/Spec.hs:56:28-56:57 }
                                  { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58, test/Plugin/Debug/Spec.hs:52:17-57:58, test/Plugin/Debug/Spec.hs:55:21-57:58, test/Plugin/Debug/Spec.hs:56:23-56:58, test/Plugin/Debug/Spec.hs:56:28-56:57 }
                                  subtractInteger
                                  { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58, test/Plugin/Debug/Spec.hs:52:17-57:58, test/Plugin/Debug/Spec.hs:55:21-57:58, test/Plugin/Debug/Spec.hs:56:23-56:58, test/Plugin/Debug/Spec.hs:56:28-56:57, test/Plugin/Debug/Spec.hs:56:54-56:54 }
                                  n
                                ]
                                (con
                                  { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58, test/Plugin/Debug/Spec.hs:52:17-57:58, test/Plugin/Debug/Spec.hs:55:21-57:58, test/Plugin/Debug/Spec.hs:56:23-56:58, test/Plugin/Debug/Spec.hs:56:28-56:57, test/Plugin/Debug/Spec.hs:56:56-56:56 }
                                  integer
                                  1
                                )
                              ]
                            ]
                          ]
                          [
                            { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58, test/Plugin/Debug/Spec.hs:52:17-57:58, test/Plugin/Debug/Spec.hs:55:21-57:58, test/Plugin/Debug/Spec.hs:57:23-57:58 }
                            { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58, test/Plugin/Debug/Spec.hs:52:17-57:58, test/Plugin/Debug/Spec.hs:55:21-57:58, test/Plugin/Debug/Spec.hs:57:23-57:58 }
                            fib
                            [
                              { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58, test/Plugin/Debug/Spec.hs:52:17-57:58, test/Plugin/Debug/Spec.hs:55:21-57:58, test/Plugin/Debug/Spec.hs:57:23-57:58, test/Plugin/Debug/Spec.hs:57:28-57:57 }
                              [
                                { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58, test/Plugin/Debug/Spec.hs:52:17-57:58, test/Plugin/Debug/Spec.hs:55:21-57:58, test/Plugin/Debug/Spec.hs:57:23-57:58, test/Plugin/Debug/Spec.hs:57:28-57:57 }
                                { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58, test/Plugin/Debug/Spec.hs:52:17-57:58, test/Plugin/Debug/Spec.hs:55:21-57:58, test/Plugin/Debug/Spec.hs:57:23-57:58, test/Plugin/Debug/Spec.hs:57:28-57:57 }
                                subtractInteger
                                { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58, test/Plugin/Debug/Spec.hs:52:17-57:58, test/Plugin/Debug/Spec.hs:55:21-57:58, test/Plugin/Debug/Spec.hs:57:23-57:58, test/Plugin/Debug/Spec.hs:57:28-57:57, test/Plugin/Debug/Spec.hs:57:54-57:54 }
                                n
                              ]
                              (con
                                { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58, test/Plugin/Debug/Spec.hs:52:17-57:58, test/Plugin/Debug/Spec.hs:55:21-57:58, test/Plugin/Debug/Spec.hs:57:23-57:58, test/Plugin/Debug/Spec.hs:57:28-57:57, test/Plugin/Debug/Spec.hs:57:56-57:56 }
                                integer
                                2
                              )
                            ]
                          ]
                        ]
                      )
                      (abs
                        { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58, test/Plugin/Debug/Spec.hs:52:17-57:58 }
                        dead
                        ({ test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58, test/Plugin/Debug/Spec.hs:52:17-57:58 }
                        type)
                        (con
                          { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58, test/Plugin/Debug/Spec.hs:52:17-57:58, test/Plugin/Debug/Spec.hs:53:24-53:24 }
                          integer
                          1
                        )
                      )
                    )
                    (all
                      { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58, test/Plugin/Debug/Spec.hs:52:17-57:58 }
                      dead
                      ({ test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58, test/Plugin/Debug/Spec.hs:52:17-57:58 }
                      type)
                      { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58, test/Plugin/Debug/Spec.hs:52:17-57:58 }
                      dead
                    )
                  }
                )
                (abs
                  { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58 }
                  dead
                  ({ test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58 }
                  type)
                  (con
                    { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58, test/Plugin/Debug/Spec.hs:50:20-50:20 }
                    integer
                    0
                  )
                )
              )
              (all
                { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58 }
                dead
                ({ test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58 }
                type)
                { test/Plugin/Debug/Spec.hs:48:11-57:58, test/Plugin/Debug/Spec.hs:49:13-57:58 }
                dead
              )
            }
          )
        )
      )
      { test/Plugin/Debug/Spec.hs:47:5-59:5 } fib
    )
  )
)