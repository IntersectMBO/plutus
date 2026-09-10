\(input : data) ->
  case
    integer
    (unListData input)
    [(\(hd : data) (tl : list data) -> unIData hd)]