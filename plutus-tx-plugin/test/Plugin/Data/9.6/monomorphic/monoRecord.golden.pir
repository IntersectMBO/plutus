let
  data MyMonoRecord | MyMonoRecord_match where
    MyMonoRecord : integer -> integer -> MyMonoRecord
in
\(ds : MyMonoRecord) ->
  MyMonoRecord_match ds {integer} (\(ipv : integer) (ipv : integer) -> ipv)