\(ds : bool) ->
  let
    !ds : bool = ds
  in
  \(ds : bool) ->
    let
      !ds : bool = ds
    in
    case (all dead. bool) ds [(/\dead -> False), (/\dead -> ds)]
      {all dead. dead}