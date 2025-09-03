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
              = case
                  (list data)
                  (unConstrData scrut)
                  [(\(l : integer) (r : list data) -> r)]
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
  let
    !tup : pair integer (list data) = unConstrData d
  in
  case
    (all dead. data)
    (equalsInteger 0 (case integer tup [(\(l : integer) (r : list data) -> l)]))
    [ (/\dead ->
         let
           !tup : pair integer (list data) = unConstrData d
         in
         case
           (all dead. data)
           (equalsInteger
              1
              (case integer tup [(\(l : integer) (r : list data) -> l)]))
           [ (/\dead ->
                let
                  !tup : pair integer (list data) = unConstrData d
                in
                case
                  (all dead. data)
                  (equalsInteger
                     2
                     (case integer tup [(\(l : integer) (r : list data) -> l)]))
                  [ (/\dead -> fail ())
                  , (/\dead ->
                       let
                         !l : list data
                           = case
                               (list data)
                               tup
                               [(\(l : integer) (r : list data) -> r)]
                       in
                       `$mInts`
                         {data}
                         (headList {data} l)
                         (\(x : integer)
                           (y : integer)
                           (z : integer)
                           (w : integer) ->
                            `$mInts`
                              {data}
                              (headList {data} (tailList {data} l))
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
                         (\(void : unit) -> fail ())) ]
                  {all dead. dead})
           , (/\dead ->
                headList
                  {data}
                  (case
                     (list data)
                     tup
                     [(\(l : integer) (r : list data) -> r)])) ]
           {all dead. dead})
    , (/\dead ->
         headList
           {data}
           (case (list data) tup [(\(l : integer) (r : list data) -> r)])) ]
    {all dead. dead}