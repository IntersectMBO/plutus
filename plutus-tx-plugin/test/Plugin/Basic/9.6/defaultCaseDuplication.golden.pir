let
  ~defaultBody : integer = 2
  data A | A_match where
    B : A
    C : A
    D : A
in
\(ds : A) ->
  let
    !ds : A = ds
  in
  A_match
    ds
    {all dead. integer}
    (/\dead -> 1)
    (/\dead -> defaultBody)
    (/\dead -> defaultBody)
    {all dead. dead}