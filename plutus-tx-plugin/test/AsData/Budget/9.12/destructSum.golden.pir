let
  data Unit | Unit_match where
    Unit : Unit
  !fail : unit -> data
    = \(ds : unit) ->
        let
          !defaultBody : data = error {data}
        in
        Unit_match (error {Unit}) {data} defaultBody
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
          let
            !l : list data
              = (let
                    b = list data
                  in
                  \(x : pair integer b) ->
                    case b x [(\(l : integer) (r : b) -> r)])
                  (unConstrData scrut)
            !l : list data = tailList {data} l
            !l : list data = tailList {data} l
          in
          cont
            (unIData (headList {data} l))
            (unIData (headList {data} l))
            (unIData (headList {data} l))
            (unIData (headList {data} (tailList {data} l)))
in
\(d : data) ->
  (let
      b = list data
    in
    /\r -> \(p : pair integer b) (f : integer -> b -> r) -> case r p [f])
    {data}
    (unConstrData d)
    (\(idx : integer) (args : list data) ->
       case
         data
         idx
         [ (headList {data} args)
         , (headList {data} args)
         , (case
              data
              args
              [ (\(hd : data) (tl : list data) ->
                   `$mInts`
                     {data}
                     hd
                     (\(x : integer)
                       (y : integer)
                       (z : integer)
                       (w : integer) ->
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
                          (\(void : unit) -> fail ()))
                     (\(void : unit) -> fail ())) ]) ])