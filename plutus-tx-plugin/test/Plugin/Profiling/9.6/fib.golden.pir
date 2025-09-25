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
  !equalsInteger : integer -> integer -> bool = equalsInteger
  ~equalsInteger : integer -> integer -> bool
    = \(x : integer) ->
        let
          !x : integer = x
        in
        \(y : integer) ->
          let
            !y : integer = y
          in
          trace
            {unit -> bool}
            "-> equalsInteger"
            (\(thunk : unit) ->
               trace {bool} "<- equalsInteger" (equalsInteger x y))
            ()
  !subtractInteger : integer -> integer -> integer = subtractInteger
  ~subtractInteger : integer -> integer -> integer
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
            "-> subtractInteger"
            (\(thunk : unit) ->
               trace {integer} "<- subtractInteger" (subtractInteger x y))
            ()
in
letrec
  ~fib : integer -> integer
    = \(n : integer) ->
        let
          !n : integer = n
        in
        trace
          {unit -> integer}
          "-> fib (test/Plugin/Profiling/Spec.hs:100:1-100:3)"
          (\(thunk : unit) ->
             trace
               {integer}
               "<- fib (test/Plugin/Profiling/Spec.hs:100:1-100:3)"
               (case
                  (all dead. integer)
                  (equalsInteger n 0)
                  [ (/\dead ->
                       case
                         (all dead. integer)
                         (equalsInteger n 1)
                         [ (/\dead ->
                              addInteger
                                (fib (subtractInteger n 1))
                                (fib (subtractInteger n 2)))
                         , (/\dead -> 1) ]
                         {all dead. dead})
                  , (/\dead -> 0) ]
                  {all dead. dead}))
          ()
in
fib