let
  !addInteger : integer -> integer -> integer
    = \(x : integer) (y : integer) -> addInteger x y
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