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
    (lam
      { no-src-span }
      ds
      (con { no-src-span } integer)
      (let
        { test/Plugin/Debug/Spec.hs:40:5-40:83 }
        (nonrec)
        (termbind
          { test/Plugin/Debug/Spec.hs:40:5-40:83 }
          (strict)
          (vardecl
            { test/Plugin/Debug/Spec.hs:40:5-40:83 }
            ds
            (con { test/Plugin/Debug/Spec.hs:40:5-40:83 } integer)
          )
          { test/Plugin/Debug/Spec.hs:40:5-40:83 } ds
        )
        (lam
          { no-src-span }
          ds
          (con { no-src-span } integer)
          (let
            { test/Plugin/Debug/Spec.hs:40:5-40:83 }
            (nonrec)
            (termbind
              { test/Plugin/Debug/Spec.hs:40:5-40:83 }
              (strict)
              (vardecl
                { test/Plugin/Debug/Spec.hs:40:5-40:83 }
                ds
                (con { test/Plugin/Debug/Spec.hs:40:5-40:83 } integer)
              )
              { test/Plugin/Debug/Spec.hs:40:5-40:83 } ds
            )
            [
              { test/Plugin/Debug/Spec.hs:40:5-40:83, test/Plugin/Debug/Spec.hs:40:40-40:82, test/Plugin/Debug/Spec.hs:40:50-40:75 }
              [
                { test/Plugin/Debug/Spec.hs:40:5-40:83, test/Plugin/Debug/Spec.hs:40:40-40:82, test/Plugin/Debug/Spec.hs:40:50-40:75 }
                { test/Plugin/Debug/Spec.hs:40:5-40:83, test/Plugin/Debug/Spec.hs:40:40-40:82, test/Plugin/Debug/Spec.hs:40:50-40:75 }
                equalsInteger
                { test/Plugin/Debug/Spec.hs:40:5-40:83, test/Plugin/Debug/Spec.hs:40:40-40:82, test/Plugin/Debug/Spec.hs:40:50-40:75, test/Plugin/Debug/Spec.hs:40:73-40:73 }
                ds
              ]
              { test/Plugin/Debug/Spec.hs:40:5-40:83, test/Plugin/Debug/Spec.hs:40:40-40:82, test/Plugin/Debug/Spec.hs:40:50-40:75, test/Plugin/Debug/Spec.hs:40:75-40:75 }
              ds
            ]
          )
        )
      )
    )
  )
)