\(ds :
    (\k a -> list (pair data data))
      bytestring
      ((\k a -> list (pair data data)) bytestring integer)) ->
  unIData
    (case
       data
       (headList
          {pair data data}
          (unMapData
             (case
                data
                (headList {pair data data} ds)
                [(\(l : data) (r : data) -> r)])))
       [(\(l : data) (r : data) -> r)])