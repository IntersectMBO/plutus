let
  data Single | Single_match where
    Single : integer -> Single
in
\(d : data) ->
  Single_match
    ((let
         b = list data
       in
       /\r ->
         \(p : pair integer b) (f : integer -> b -> r) ->
           f (fstPair {integer} {b} p) (sndPair {integer} {b} p))
       {Single}
       (unConstrData d)
       (\(index : integer) (args : list data) ->
          ifThenElse
            {all dead. list data -> Single}
            (equalsInteger 0 index)
            (/\dead ->
               \(ds : list data) -> Single (unIData (headList {data} ds)))
            (/\dead -> error {list data -> Single})
            {list data -> Single}
            args))
    {integer}
    (\(x : integer) -> x)