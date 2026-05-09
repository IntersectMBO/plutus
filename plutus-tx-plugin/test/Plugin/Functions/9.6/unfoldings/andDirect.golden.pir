let
  ~andDirect : bool -> bool -> bool
    = \(ds : bool) ->
        let
          !ds : bool = ds
        in
        \(ds : bool) ->
          let
            !ds : bool = ds
          in
          (let
              !ds : bool
                = case
                    (all dead. bool)
                    ds
                    [(/\dead -> case bool ds [True, False]), (/\dead -> False)]
                    {all dead. dead}
            in
            \(ds : bool) ->
              let
                !ds : bool = ds
              in
              case
                (all dead. bool)
                ds
                [(/\dead -> case bool ds [True, False]), (/\dead -> False)]
                {all dead. dead})
            (case
               (all dead. bool)
               ds
               [(/\dead -> case bool ds [True, False]), (/\dead -> False)]
               {all dead. dead})
in
andDirect True False