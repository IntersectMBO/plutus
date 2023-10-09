-- the constant 5 should turn into the first argument of ((==) (10+2)) 5)
-- this tests that the function works on equalInteger

[
    [ (builtin equalsInteger)  
        [
            [(builtin addInteger) (con integer 10)] (con integer 2)
        ]
    ] (con integer 5)
]