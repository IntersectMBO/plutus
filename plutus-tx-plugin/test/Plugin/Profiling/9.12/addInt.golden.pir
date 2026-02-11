let
  !addInteger : integer -> integer -> integer = addInteger
  ~addInteger : integer -> integer -> integer
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) ->
          let
            !y : integer = y
          in
          trace
            {unit -> integer}
            "-> addInteger"
            (\(thunk : unit) ->
               trace {integer} "<- addInteger" (addInteger x y))
            ()
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
               (addInteger x))
          ()
in
addInt