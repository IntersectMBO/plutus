let
  RecordNewtype = all a. a -> a
  MyMonoRecord = all a. a -> a
  data RecordWithStrictField | RecordWithStrictField_match where
    RecordWithStrictField :
      MyMonoRecord -> RecordNewtype -> RecordWithStrictField
  ~strictField : RecordWithStrictField -> RecordNewtype
    = \(ds : RecordWithStrictField) ->
        RecordWithStrictField_match
          ds
          {RecordNewtype}
          (\(ds : MyMonoRecord) (ds : RecordNewtype) -> ds)
in
\(ds : RecordWithStrictField) ->
  let
    !ds : RecordWithStrictField = ds
  in
  strictField ds