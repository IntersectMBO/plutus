(program
  1.1.0
  [
    [
      [
        [
          [ (lam simpleList (lam simplePair (lam nestedList (lam twoDArray (lam str (con unit ()) )))))
            (con
              (list integer)
              [1 , 2 , 3 , 4]
            )
          ]
          (con (pair integer bool) (1 , True) )
        ]
        (con
          (list (pair integer (list bool)))
          [(1 , [True]), (2, [False , True]), (100, []), (123423, [False, False, False, False])]
        )
      ]
      (con (array (array integer)) [[1 , 2 , 3] , [4 , 5 , 6] , [7 , 8 , 9]])
    ]
    (con string "hello, world")
  ]
)