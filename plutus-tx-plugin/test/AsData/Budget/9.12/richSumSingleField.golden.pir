\(d : data) ->
  (let
      b = list data
    in
    /\r -> \(p : pair integer b) (f : integer -> b -> r) -> case r p [f])
    {integer}
    (unConstrData d)
    (\(idx : integer)
      (args : list data) ->
       case
         integer
         idx
         [ (case
              integer
              args
              [ (\(hd : data) (tl : list data) ->
                   case
                     integer
                     tl
                     [ (\(hd : data) (tl : list data) ->
                          case
                            integer
                            tl
                            [ (\(hd : data) (tl : list data) ->
                                 case
                                   integer
                                   tl
                                   [ (\(hd : data) (tl : list data) ->
                                        case
                                          integer
                                          tl
                                          [ (\(hd : data) (tl : list data) ->
                                               unIData hd) ]) ]) ]) ]) ])
         , (case
              integer
              args
              [ (\(hd : data) (tl : list data) ->
                   case
                     integer
                     tl
                     [ (\(hd : data) (tl : list data) ->
                          case
                            integer
                            tl
                            [ (\(hd : data) (tl : list data) ->
                                 case
                                   integer
                                   tl
                                   [ (\(hd : data) (tl : list data) ->
                                        case
                                          integer
                                          tl
                                          [ (\(hd : data) (tl : list data) ->
                                               case
                                                 integer
                                                 tl
                                                 [ (\(hd : data)
                                                     (tl : list data) ->
                                                      unIData
                                                        hd) ]) ]) ]) ]) ]) ])
         , (case
              integer
              args
              [ (\(hd : data)
                  (tl : list data) ->
                   case
                     integer
                     tl
                     [ (\(hd : data)
                         (tl : list data) ->
                          case
                            integer
                            tl
                            [ (\(hd : data)
                                (tl : list data) ->
                                 case
                                   integer
                                   tl
                                   [ (\(hd : data)
                                       (tl : list data) ->
                                        case
                                          integer
                                          tl
                                          [ (\(hd : data)
                                              (tl : list data) ->
                                               case
                                                 integer
                                                 tl
                                                 [ (\(hd : data)
                                                     (tl : list data) ->
                                                      case
                                                        integer
                                                        tl
                                                        [ (\(hd : data)
                                                            (tl : list data) ->
                                                             unIData
                                                               hd) ]) ]) ]) ]) ]) ]) ]) ])