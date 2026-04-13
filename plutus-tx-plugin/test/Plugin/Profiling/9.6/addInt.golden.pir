let
  !addInteger : integer -> integer -> integer = addInteger
  ~addInt : integer -> integer -> integer
    = \(x : integer) ->
        let
          !x : integer = x
        in
        trace
          {unit -> integer -> integer}
          "-> addInt (test/Plugin/Profiling/Spec.hs:116:1-116:6)"
          (\(thunk : unit) ->
             trace
               {integer -> integer}
               "<- addInt (test/Plugin/Profiling/Spec.hs:116:1-116:6)"
               (\(y : integer) -> let !y : integer = y in addInteger x y))
          ()
in
addInt