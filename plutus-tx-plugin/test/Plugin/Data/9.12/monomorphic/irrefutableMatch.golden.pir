let
  ~defaultBody : integer = (/\e -> error {e}) {integer}
  data Unit | Unit_match where
    Unit : Unit
  ~defaultBody : integer
    = Unit_match ((/\e -> error {e}) {Unit}) {integer} defaultBody
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
    (\(a : integer) -> a)
    (\(default_arg0 : integer) -> defaultBody)