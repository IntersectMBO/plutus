let
  data Single | Single_match where
    Single : integer -> Single
in
\(d : data) ->
  Single_match
    (case
       Single
       d
       [(\(ds : list data) -> Single (unIData (headList {data} ds)))])
    {integer}
    (\(x : integer) -> x)