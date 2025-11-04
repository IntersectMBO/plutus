let
  data MyMonoRecord | MyMonoRecord_match where
    MyMonoRecord : integer -> integer -> MyMonoRecord
  ~mrA : MyMonoRecord -> integer
    = \(ds : MyMonoRecord) ->
        MyMonoRecord_match ds {integer} (\(ds : integer) (ds : integer) -> ds)
in
\(ds : MyMonoRecord) -> let !ds : MyMonoRecord = ds in mrA ds