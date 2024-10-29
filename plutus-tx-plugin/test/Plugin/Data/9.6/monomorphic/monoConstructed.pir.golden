let
  data MyMonoData | MyMonoData_match where
    Mono : integer -> integer -> MyMonoData
    Mono : integer -> MyMonoData
    Mono : integer -> MyMonoData
  ~`$WMono` : integer -> MyMonoData
    = \(conrep : integer) -> let !conrep : integer = conrep in Mono conrep
in
`$WMono` 1