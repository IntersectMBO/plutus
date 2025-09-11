let
  ~defaultBody : integer = 1
  data MyMonoData | MyMonoData_match where
    Mono : integer -> integer -> MyMonoData
    Mono : integer -> MyMonoData
    Mono : integer -> MyMonoData
in
\(ds : MyMonoData) ->
  let
    !ds : MyMonoData = ds
  in
  MyMonoData_match
    ds
    {integer}
    (\(default_arg0 : integer) (default_arg1 : integer) -> defaultBody)
    (\(i : integer) -> i)
    (\(default_arg0 : integer) -> defaultBody)