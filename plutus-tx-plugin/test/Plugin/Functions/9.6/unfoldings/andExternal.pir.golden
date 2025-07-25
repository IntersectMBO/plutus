let
  ~andExternal : bool -> bool -> bool
    = \(a : bool) ->
        let
          !a : bool = a
        in
        \(b : bool) ->
          let
            !b : bool = b
          in
          case (all dead. bool) a [(/\dead -> False), (/\dead -> b)]
            {all dead. dead}
in
andExternal True False