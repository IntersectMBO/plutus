let
  !addInteger : integer -> integer -> integer
    = \(x : integer) (y : integer) -> addInteger x y
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
                = (let
                      b = list data
                    in
                    \(x : pair integer b) ->
                      case b x [(\(l : integer) (r : b) -> r)])
                    (unConstrData scrut)
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
  !int : data -> integer
    = \(ds : data) ->
        `$mInts`
          {integer}
          ds
          (\(ds : integer) (ds : integer) (ds : integer) (ds : integer) -> ds)
          (\(void : unit) -> error {integer})
  !int : data -> integer
    = \(ds : data) ->
        `$mInts`
          {integer}
          ds
          (\(ds : integer) (ds : integer) (ds : integer) (ds : integer) -> ds)
          (\(void : unit) -> error {integer})
  !int : data -> integer
    = \(ds : data) ->
        `$mInts`
          {integer}
          ds
          (\(ds : integer) (ds : integer) (ds : integer) (ds : integer) -> ds)
          (\(void : unit) -> error {integer})
  !int : data -> integer
    = \(ds : data) ->
        `$mInts`
          {integer}
          ds
          (\(ds : integer) (ds : integer) (ds : integer) (ds : integer) -> ds)
          (\(void : unit) -> error {integer})
  !lessThanInteger : integer -> integer -> bool
    = \(x : integer) (y : integer) -> lessThanInteger x y
in
\(d : data) ->
  let
    !x : integer = int d
    !y : integer = int d
    !z : integer = int d
    !w : integer = int d
  in
  addInteger
    (addInteger
       (addInteger (addInteger (addInteger x y) z) w)
       (case
          (all dead. integer)
          (lessThanInteger (addInteger y z) (addInteger x w))
          [(/\dead -> addInteger y w), (/\dead -> addInteger x z)]
          {all dead. dead}))
    (case
       (all dead. integer)
       (lessThanInteger
          (addInteger (int d) (int d))
          (addInteger (int d) (int d)))
       [ (/\dead -> addInteger (int d) (int d))
       , (/\dead -> addInteger (int d) (int d)) ]
       {all dead. dead})