let
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
    (\(ds : integer) (b : integer) -> b)
    (\(a : integer) -> a)
    (\(a : integer) -> a)