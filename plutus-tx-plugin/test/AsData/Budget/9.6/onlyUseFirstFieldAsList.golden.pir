\(input : data) ->
  case
    integer
    (unListData input)
    [(\(ds : data) (ds : list data) -> unIData ds)]