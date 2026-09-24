let
  !trace : all a. string -> a -> a = trace
  ~trace : all a. string -> a -> a = trace
in
\(ds : string) -> let !ds : string = ds in trace {unit} ds ()