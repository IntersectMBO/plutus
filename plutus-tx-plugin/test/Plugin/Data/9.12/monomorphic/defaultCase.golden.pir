let
  ~defaultBody : integer = 2
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
    (\(default_arg0 : integer) -> defaultBody)
    (\(a : integer) -> a)