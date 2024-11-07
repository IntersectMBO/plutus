let
  data MyExternalRecord | MyExternalRecord_match where
    MyExternalRecord : integer -> MyExternalRecord
  ~myExternal : MyExternalRecord -> integer
    = \(ds : MyExternalRecord) ->
        MyExternalRecord_match ds {integer} (\(ds : integer) -> ds)
in
\(ds : MyExternalRecord) -> let !ds : MyExternalRecord = ds in myExternal ds