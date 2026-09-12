\(i : integer) ->
  let
    !caseIntegerScrutinee : integer
      = trace
          {integer}
          "scrutinee"
          (divideInteger (addInteger (multiplyInteger i i) i) 3)
  in
  ifThenElse
    {all dead. string}
    (equalsInteger 0 caseIntegerScrutinee)
    (/\dead -> trace {string} "branch 0" "a")
    (/\dead ->
       ifThenElse
         {all dead. string}
         (equalsInteger 1 caseIntegerScrutinee)
         (/\dead -> trace {string} "branch 1" "b")
         (/\dead ->
            ifThenElse
              {all dead. string}
              (equalsInteger 2 caseIntegerScrutinee)
              (/\dead -> trace {string} "branch 2" "c")
              (/\dead -> error {string})
              {string})
         {string})
    {string}