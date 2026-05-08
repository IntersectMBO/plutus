let
  !addInteger : integer -> integer -> integer = addInteger
  !equalsInteger : integer -> integer -> bool = equalsInteger
  !subtractInteger : integer -> integer -> integer = subtractInteger
in
letrec
  ~fib : integer -> integer
    = \(n : integer) ->
        let
          !n : integer = n
        in
        trace
          {unit -> integer}
          "-> fib (test/Plugin/Profiling/Spec.hs:99:1-99:3)"
          (\(thunk : unit) ->
             trace
               {integer}
               "<- fib (test/Plugin/Profiling/Spec.hs:99:1-99:3)"
               (case
                  (all dead. integer)
                  (equalsInteger n 0)
                  [ (/\dead ->
                       case
                         (all dead. integer)
                         (equalsInteger n 1)
                         [ (/\dead ->
                              let
                                !x : integer = fib (subtractInteger n 1)
                                !y : integer = fib (subtractInteger n 2)
                              in
                              addInteger x y)
                         , (/\dead -> 1) ]
                         {all dead. dead})
                  , (/\dead -> 0) ]
                  {all dead. dead}))
          ()
in
fib