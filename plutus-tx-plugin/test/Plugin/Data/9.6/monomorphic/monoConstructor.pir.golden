let
  data MyMonoData | MyMonoData_match where
    Mono : integer -> integer -> MyMonoData
    Mono : integer -> MyMonoData
    Mono : integer -> MyMonoData
  ~`$WMono` : integer -> integer -> MyMonoData
    = \(conrep : integer) ->
        let
          !conrep : integer = conrep
        in
        \(conrep : integer) ->
          let
            !conrep : integer = conrep
          in
          Mono conrep conrep
in
\(ds : integer) (ds : integer) -> `$WMono` ds ds