let
  !`$mInts` :
     all r.
       data ->
       (integer -> integer -> integer -> integer -> r) ->
       (unit -> r) ->
       r
    = /\r ->
        \(scrut : data)
         (cont : integer -> integer -> integer -> integer -> r)
         (fail : unit -> r) ->
          case
            r
            ((let
                 b = list data
               in
               \(x : pair integer b) ->
                 case b x [(\(l : integer) (r : b) -> r)])
               (unConstrData scrut))
            [ (\(ds : data) (ds : list data) ->
                 case
                   r
                   ds
                   [ (\(ds : data) (ds : list data) ->
                        case
                          r
                          ds
                          [ (\(ds : data) (ds : list data) ->
                               cont
                                 (unIData ds)
                                 (unIData ds)
                                 (unIData ds)
                                 (unIData (headList {data} ds))) ]) ]) ]
in
\(d : data) ->
  case
    data
    d
    [ (\(args : list data) -> headList {data} args)
    , (\(args : list data) -> headList {data} args)
    , (\(args : list data) ->
         case
           data
           args
           [ (\(hd : data) (tl : list data) ->
                `$mInts`
                  {data}
                  hd
                  (\(x : integer) (y : integer) (z : integer) (w : integer) ->
                     `$mInts`
                       {data}
                       (headList {data} tl)
                       (\(x : integer)
                         (y : integer)
                         (z : integer)
                         (w : integer) ->
                          constrData
                            0
                            (mkCons
                               {data}
                               (iData (addInteger x x))
                               (mkCons
                                  {data}
                                  (iData (addInteger y y))
                                  (mkCons
                                     {data}
                                     (iData (addInteger z z))
                                     (mkCons
                                        {data}
                                        (iData (addInteger w w))
                                        [])))))
                       (\(void : unit) ->
                          case data (error {unit}) [(error {data})]))
                  (\(void : unit) ->
                     case data (error {unit}) [(error {data})])) ]) ]