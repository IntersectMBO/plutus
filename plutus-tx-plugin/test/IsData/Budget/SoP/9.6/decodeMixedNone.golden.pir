let
  data Mixed | Mixed_match where
    MNone : Mixed
    MOne : integer -> Mixed
    MTwo : integer -> integer -> Mixed
in
\(d : data) ->
  Mixed_match
    ((let
         b = list data
       in
       /\r ->
         \(p : pair integer b) (f : integer -> b -> r) ->
           f (fstPair {integer} {b} p) (sndPair {integer} {b} p))
       {Mixed}
       (unConstrData d)
       (\(index : integer) (args : list data) ->
          ifThenElse
            {all dead. list data -> Mixed}
            (equalsInteger 0 index)
            (/\dead -> \(ds : list data) -> MNone)
            (/\dead ->
               ifThenElse
                 {all dead. list data -> Mixed}
                 (equalsInteger 1 index)
                 (/\dead ->
                    \(ds : list data) -> MOne (unIData (headList {data} ds)))
                 (/\dead ->
                    ifThenElse
                      {all dead. list data -> Mixed}
                      (equalsInteger 2 index)
                      (/\dead ->
                         \(ds : list data) ->
                           MTwo
                             (unIData (headList {data} ds))
                             (unIData (headList {data} (tailList {data} ds))))
                      (/\dead -> error {list data -> Mixed})
                      {list data -> Mixed})
                 {list data -> Mixed})
            {list data -> Mixed}
            args))
    {integer}
    0
    (\(x : integer) -> x)
    (\(x : integer) (y : integer) -> addInteger x y)