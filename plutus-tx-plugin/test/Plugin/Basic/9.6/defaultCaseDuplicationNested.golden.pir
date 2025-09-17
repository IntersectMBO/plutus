let
  ~defaultBody : integer = 3
  data A | A_match where
    B : A
    C : A
    D : A
in
\(ds : A) ->
  let
    !ds : A = ds
  in
  \(ds : A) ->
    let
      !ds : A = ds
      ~defaultBody : integer
        = A_match
            ds
            {all dead. integer}
            (/\dead -> 2)
            (/\dead -> defaultBody)
            (/\dead -> defaultBody)
            {all dead. dead}
    in
    A_match
      ds
      {all dead. integer}
      (/\dead -> 1)
      (/\dead -> defaultBody)
      (/\dead -> defaultBody)
      {all dead. dead}