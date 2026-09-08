\(d : data) ->
  let
    !d : data = d
    !dataConstr : pair integer (list data) = unConstrData d
  in
  ifThenElse
    {all dead. list data -> list data}
    (equalsInteger 0 (fstPair {integer} {list data} dataConstr))
    (/\dead -> \(xs : list data) -> xs)
    (/\dead -> error {list data -> list data})
    {list data -> list data}
    (sndPair {integer} {list data} dataConstr)