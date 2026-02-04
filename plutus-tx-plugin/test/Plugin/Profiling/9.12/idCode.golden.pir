let
  ~id : all a. a -> a
    = /\a ->
        \(x : a) ->
          trace {unit -> a} "-> id" (\(thunk : unit) -> trace {a} "<- id" x) ()
in
id {integer} (id {integer} 1)