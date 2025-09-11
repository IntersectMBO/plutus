\(d : data) ->
  let
    !nt : list data = tailList {data} (unListData d)
    !s : integer = unIData (headList {data} nt)
    !nt : list data = tailList {data} (tailList {data} (tailList {data} nt))
    !s : integer = unIData (headList {data} nt)
    !s : integer = unIData (headList {data} (tailList {data} nt))
  in
  addInteger (addInteger s s) s