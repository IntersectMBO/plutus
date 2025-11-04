let
  data (Tuple2 :: * -> * -> *) a b | Tuple2_match where
    Tuple2 : a -> b -> Tuple2 a b
in
\(l : (\a -> list data) integer) ->
  letrec
    !go : list data -> Tuple2 (list data) (list data)
      = (let
            r = Tuple2 (list data) (list data)
          in
          \(z : r) (f : data -> list data -> r) (xs : list data) ->
            case r xs [f, z])
          (Tuple2 {list data} {list data} [] [])
          (\(h : data) (t : list data) ->
             Tuple2_match
               {list data}
               {list data}
               (go t)
               {Tuple2 (list data) (list data)}
               (\(ipv : list data) (ipv : list data) ->
                  case
                    (all dead. Tuple2 (list data) (list data))
                    (case bool (lessThanInteger (unIData h) 8) [True, False])
                    [ (/\dead ->
                         Tuple2
                           {list data}
                           {list data}
                           ipv
                           (mkCons {data} h ipv))
                    , (/\dead ->
                         Tuple2
                           {list data}
                           {list data}
                           (mkCons {data} h ipv)
                           ipv) ]
                    {all dead. dead}))
  in
  go l