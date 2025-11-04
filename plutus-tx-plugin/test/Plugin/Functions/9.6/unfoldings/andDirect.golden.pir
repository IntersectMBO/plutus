let
  ~nandDirect : bool -> bool -> bool
    = \(ds : bool) ->
        let
          !ds : bool = ds
        in
        \(ds : bool) ->
          let
            !ds : bool = ds
          in
          case
            (all dead. bool)
            ds
            [(/\dead -> case bool ds [True, False]), (/\dead -> False)]
            {all dead. dead}
  ~andDirect : bool -> bool -> bool
    = \(ds : bool) ->
        let
          !ds : bool = ds
        in
        \(ds : bool) ->
          let
            !ds : bool = ds
          in
          nandDirect (nandDirect ds ds) (nandDirect ds ds)
in
andDirect True False