letrec
  !last : all a. list a -> a
    = /\a ->
        \(eta : list a) ->
          case
            (unit -> a)
            eta
            [ (\(x : a) (xs : list a) (ds : unit) ->
                 case a xs [(\(ds : a) (ds : list a) -> last {a} xs), x])
            , (\(ds : unit) ->
                 let
                   !x : unit = trace {unit} "PT25" ()
                 in
                 error {a}) ]
            ()
in
\(xs : list integer) -> last {integer} xs