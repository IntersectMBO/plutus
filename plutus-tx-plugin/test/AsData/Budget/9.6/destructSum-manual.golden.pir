let
  data Unit | Unit_match where
    Unit : Unit
  !fail : unit -> data
    = \(ds : unit) ->
        let
          !defaultBody : data = error {data}
        in
        Unit_match (error {Unit}) {data} defaultBody
  !`$fUnsafeFromDataBuiltinData_$cunsafeFromBuiltinData` : data -> data
    = \(d : data) -> d
  data (Tuple2 :: * -> * -> *) a b | Tuple2_match where
    Tuple2 : a -> b -> Tuple2 a b
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
          Tuple2_match
            {data}
            {list data}
            (let
              !l : list data
                = case
                    (list data)
                    (unConstrData scrut)
                    [(\(l : integer) (r : list data) -> r)]
            in
            Tuple2 {data} {list data} (headList {data} l) (tailList {data} l))
            {r}
            (\(ds : data) (ds : list data) ->
               let
                 !ds : data = headList {data} ds
                 !ds : list data = tailList {data} ds
                 !ds : data = headList {data} ds
                 !ds : list data = tailList {data} ds
               in
               cont
                 (unIData ds)
                 (unIData ds)
                 (unIData ds)
                 (unIData (headList {data} ds)))
  !unpack : all a. (\a -> data -> a) a -> list data -> a
    = /\a ->
        \(`$dUnsafeFromData` : (\a -> data -> a) a) ->
          (let
              a = list data
            in
            \(f : data -> a) (g : a -> data) (x : a) -> f (g x))
            `$dUnsafeFromData`
            (headList {data})
in
\(d : data) ->
  Tuple2_match
    {integer}
    {list data}
    ((let
         b = list data
       in
       \(tup : pair integer b) ->
         Tuple2
           {integer}
           {b}
           (case integer tup [(\(l : integer) (r : b) -> l)])
           (case b tup [(\(l : integer) (r : b) -> r)]))
       (unConstrData d))
    {data}
    (\(ds : integer)
      (ds : list data) ->
       case
         (all dead. data)
         (equalsInteger 0 ds)
         [ (/\dead ->
              Tuple2_match
                {integer}
                {list data}
                ((let
                     b = list data
                   in
                   \(tup : pair integer b) ->
                     Tuple2
                       {integer}
                       {b}
                       (case integer tup [(\(l : integer) (r : b) -> l)])
                       (case b tup [(\(l : integer) (r : b) -> r)]))
                   (unConstrData d))
                {data}
                (\(ds : integer)
                  (ds : list data) ->
                   case
                     (all dead. data)
                     (equalsInteger 1 ds)
                     [ (/\dead ->
                          Tuple2_match
                            {integer}
                            {list data}
                            ((let
                                 b = list data
                               in
                               \(tup : pair integer b) ->
                                 Tuple2
                                   {integer}
                                   {b}
                                   (case
                                      integer
                                      tup
                                      [(\(l : integer) (r : b) -> l)])
                                   (case b tup [(\(l : integer) (r : b) -> r)]))
                               (unConstrData d))
                            {data}
                            (\(ds : integer)
                              (ds : list data) ->
                               case
                                 (all dead. data)
                                 (equalsInteger 2 ds)
                                 [ (/\dead -> fail ())
                                 , (/\dead ->
                                      Tuple2_match
                                        {data}
                                        {data}
                                        (let
                                          !y : data
                                            = headList
                                                {data}
                                                (tailList {data} ds)
                                        in
                                        Tuple2
                                          {data}
                                          {data}
                                          (headList {data} ds)
                                          y)
                                        {data}
                                        (\(arg : data)
                                          (arg : data) ->
                                           `$mInts`
                                             {data}
                                             arg
                                             (\(x : integer)
                                               (y : integer)
                                               (z : integer)
                                               (w : integer) ->
                                                `$mInts`
                                                  {data}
                                                  arg
                                                  (\(x : integer)
                                                    (y : integer)
                                                    (z : integer)
                                                    (w : integer) ->
                                                     constrData
                                                       0
                                                       (mkCons
                                                          {data}
                                                          (iData
                                                             (addInteger x x))
                                                          (mkCons
                                                             {data}
                                                             (iData
                                                                (addInteger
                                                                   y
                                                                   y))
                                                             (mkCons
                                                                {data}
                                                                (iData
                                                                   (addInteger
                                                                      z
                                                                      z))
                                                                (mkCons
                                                                   {data}
                                                                   (iData
                                                                      (addInteger
                                                                         w
                                                                         w))
                                                                   [])))))
                                                  (\(void : unit) -> fail ()))
                                             (\(void : unit) -> fail ()))) ]
                                 {all dead. dead}))
                     , (/\dead ->
                          unpack
                            {data}
                            `$fUnsafeFromDataBuiltinData_$cunsafeFromBuiltinData`
                            ds) ]
                     {all dead. dead}))
         , (/\dead ->
              unpack
                {data}
                `$fUnsafeFromDataBuiltinData_$cunsafeFromBuiltinData`
                ds) ]
         {all dead. dead})