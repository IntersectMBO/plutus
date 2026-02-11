let
  data MyMonoRecordAsList | MyMonoRecordAsList_match where
    MyMonoRecordAsList : integer -> integer -> MyMonoRecordAsList
  !mkCons : all a. a -> list a -> list a = mkCons
  !mkI : integer -> data = iData
  !mkList : list data -> data = listData
  !mkNilData : unit -> list data = mkNilData
  !unitval : unit = ()
  ~`$ctoBuiltinData` : MyMonoRecordAsList -> data
    = \(ds : MyMonoRecordAsList) ->
        MyMonoRecordAsList_match
          ds
          {data}
          (\(arg : integer) (arg : integer) ->
             mkList
               (mkCons
                  {data}
                  (mkI arg)
                  (mkCons {data} (mkI arg) (mkNilData unitval))))
  ~`$fToDataMyMonoRecordAsList` : (\a -> a -> data) MyMonoRecordAsList
    = `$ctoBuiltinData`
  ~toBuiltinData : all a. (\a -> a -> data) a -> a -> data
    = /\a -> \(v : (\a -> a -> data) a) -> v
in
toBuiltinData {MyMonoRecordAsList} `$fToDataMyMonoRecordAsList`