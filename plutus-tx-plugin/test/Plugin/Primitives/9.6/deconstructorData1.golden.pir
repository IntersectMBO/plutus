let
  !unsafeDataAsI : data -> integer = unIData
  ~unsafeDataAsI : data -> integer
    = \(d : data) -> let !d : data = d in unsafeDataAsI d
in
\(ds : data) -> let !ds : data = ds in unsafeDataAsI ds