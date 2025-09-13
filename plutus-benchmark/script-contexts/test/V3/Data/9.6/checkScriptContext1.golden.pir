(letrec
    !go : list data -> integer
      = \(xs : list data) ->
          case
            integer
            xs
            [(\(ds : data) (eta : list data) -> addInteger 1 (go eta)), 0]
  in
  let
    data (Maybe :: * -> *) a | Maybe_match where
      Just : a -> Maybe a
      Nothing : Maybe a
    !`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData` :
       all a. (\a -> data -> a) a -> data -> Maybe a
      = /\a ->
          \(`$dUnsafeFromData` : (\a -> data -> a) a) (d : data) ->
            (let
                b = list data
              in
              /\r ->
                \(p : pair integer b) (f : integer -> b -> r) -> case r p [f])
              {Maybe a}
              (unConstrData d)
              (\(index : integer) (args : list data) ->
                 case
                   (list data -> Maybe a)
                   index
                   [ (\(ds : list data) ->
                        Just {a} (`$dUnsafeFromData` (headList {data} ds)))
                   , (\(ds : list data) -> Nothing {a}) ]
                   args)
    data Unit | Unit_match where
      Unit : Unit
    data (Solo :: * -> *) a | Solo_match where
      MkSolo : a -> Solo a
  in
  \(d : data) ->
    Solo_match
      {data}
      ((let
           r = Solo data
         in
         \(scrut : data)
          (cont : data -> data -> data -> r)
          (fail : unit -> r) ->
           let
             !l : list data
               = case
                   (list data)
                   (unConstrData scrut)
                   [(\(l : integer) (r : list data) -> r)]
             !l : list data = tailList {data} l
           in
           cont
             (headList {data} l)
             (headList {data} l)
             (headList {data} (tailList {data} l)))
         d
         (\(txi : data) (ds : data) (ds : data) -> MkSolo {data} txi)
         (\(void : unit) ->
            let
              !defaultBody : Solo data = error {Solo data}
            in
            Unit_match (error {Unit}) {Solo data} defaultBody))
      {Unit}
      (\(ipv : data) ->
         case
           (all dead. Unit)
           (equalsInteger
              0
              (modInteger
                 (let
                   !ds : (\a -> list data) data
                     = (let
                           r = (\a -> list data) data
                         in
                         \(scrut : data)
                          (cont :
                             (\a -> list data) data ->
                             (\a -> list data) data ->
                             (\a -> list data) data ->
                             integer ->
                             (\k a -> list (pair data data))
                               bytestring
                               ((\k a -> list (pair data data))
                                  bytestring
                                  integer) ->
                             (\a -> list data) data ->
                             (\k a -> list (pair data data)) data integer ->
                             (\a -> data) integer ->
                             (\a -> list data) bytestring ->
                             (\k a -> list (pair data data)) data data ->
                             (\k a -> list (pair data data)) bytestring data ->
                             bytestring ->
                             (\k a -> list (pair data data))
                               data
                               ((\k a -> list (pair data data)) data data) ->
                             (\a -> list data) data ->
                             Maybe integer ->
                             Maybe integer ->
                             r)
                          (fail : unit -> r) ->
                           let
                             !l : list data
                               = case
                                   (list data)
                                   (unConstrData scrut)
                                   [(\(l : integer) (r : list data) -> r)]
                             !l : list data = tailList {data} l
                             !l : list data = tailList {data} l
                             !l : list data = tailList {data} l
                             !l : list data = tailList {data} l
                             !l : list data = tailList {data} l
                             !l : list data = tailList {data} l
                             !l : list data = tailList {data} l
                             !l : list data = tailList {data} l
                             !l : list data = tailList {data} l
                             !l : list data = tailList {data} l
                             !l : list data = tailList {data} l
                             !l : list data = tailList {data} l
                             !l : list data = tailList {data} l
                             !l : list data = tailList {data} l
                           in
                           cont
                             (unListData (headList {data} l))
                             (unListData (headList {data} l))
                             (unListData (headList {data} l))
                             (unIData (headList {data} l))
                             (unMapData (headList {data} l))
                             (unListData (headList {data} l))
                             (unMapData (headList {data} l))
                             (headList {data} l)
                             (unListData (headList {data} l))
                             (unMapData (headList {data} l))
                             (unMapData (headList {data} l))
                             (unBData (headList {data} l))
                             (unMapData (headList {data} l))
                             (unListData (headList {data} l))
                             (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                                {integer}
                                unIData
                                (headList {data} l))
                             (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                                {integer}
                                unIData
                                (headList {data} (tailList {data} l))))
                         ipv
                         (\(ds : (\a -> list data) data)
                           (ds : (\a -> list data) data)
                           (ds : (\a -> list data) data)
                           (ds : integer)
                           (ds :
                              (\k a -> list (pair data data))
                                bytestring
                                ((\k a -> list (pair data data))
                                   bytestring
                                   integer))
                           (ds : (\a -> list data) data)
                           (ds : (\k a -> list (pair data data)) data integer)
                           (ds : (\a -> data) integer)
                           (ds : (\a -> list data) bytestring)
                           (ds : (\k a -> list (pair data data)) data data)
                           (ds :
                              (\k a -> list (pair data data)) bytestring data)
                           (ds : bytestring)
                           (ds :
                              (\k a -> list (pair data data))
                                data
                                ((\k a -> list (pair data data)) data data))
                           (ds : (\a -> list data) data)
                           (ds : Maybe integer)
                           (ds : Maybe integer) ->
                            ds)
                         (\(void : unit) -> error {(\a -> list data) data})
                 in
                 go ds)
                 2))
           [ (/\dead ->
                let
                  !x : Unit = trace {Unit} "Odd number of outputs" Unit
                in
                error {Unit})
           , (/\dead -> Unit) ]
           {all dead. dead}))
  (Constr 0
     [ Constr 0
         [ List []
         , List []
         , List
             [ Constr 0
                 [ Constr 0 [Constr 0 [B #], Constr 1 []]
                 , Map [(B #, Map [(B #, I 1)])]
                 , Constr 0 []
                 , Constr 1 [] ] ]
         , I 10000
         , Map []
         , List []
         , Map []
         , Constr 0
             [ Constr 0 [Constr 0 [], Constr 1 []]
             , Constr 0 [Constr 2 [], Constr 1 []] ]
         , List []
         , Map []
         , Map []
         , B #
         , Map []
         , List []
         , Constr 1 []
         , Constr 1 [] ]
     , I 1
     , Constr 1 [Constr 0 [B #, I 0], Constr 1 []] ])