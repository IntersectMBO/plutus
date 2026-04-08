let
  data ABC | ABC_match where
    A : integer -> ABC
    B : integer -> ABC
    C : integer -> ABC
in
\(d : data) ->
  ABC_match
    ((let
         b = list data
       in
       /\r ->
         \(p : pair integer b) (f : integer -> b -> r) ->
           f (fstPair {integer} {b} p) (sndPair {integer} {b} p))
       {ABC}
       (unConstrData d)
       (\(index : integer) (args : list data) ->
          ifThenElse
            {all dead. list data -> ABC}
            (equalsInteger 0 index)
            (/\dead -> \(ds : list data) -> A (unIData (headList {data} ds)))
            (/\dead ->
               ifThenElse
                 {all dead. list data -> ABC}
                 (equalsInteger 1 index)
                 (/\dead ->
                    \(ds : list data) -> B (unIData (headList {data} ds)))
                 (/\dead ->
                    ifThenElse
                      {all dead. list data -> ABC}
                      (equalsInteger 2 index)
                      (/\dead ->
                         \(ds : list data) -> C (unIData (headList {data} ds)))
                      (/\dead -> error {list data -> ABC})
                      {list data -> ABC})
                 {list data -> ABC})
            {list data -> ABC}
            args))
    {integer}
    (\(x : integer) -> x)
    (\(x : integer) -> addInteger 100 x)
    (\(x : integer) -> addInteger 200 x)