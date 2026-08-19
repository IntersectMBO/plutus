letrec
  data (List :: * -> *) a | List_match where
    Nil : List a
    Cons : a -> List a -> List a
in
let
  data Unit | Unit_match where
    Unit : Unit
in
letrec
  !go : integer -> List data -> data
    = \(ds : integer) (ds : List data) ->
        List_match
          {data}
          ds
          {all dead. data}
          (/\dead -> let !x : Unit = trace {Unit} "PT7" Unit in error {data})
          (\(x : data) (xs : List data) ->
             /\dead ->
               case
                 (all dead. data)
                 (equalsInteger 0 ds)
                 [(/\dead -> go (subtractInteger ds 1) xs), (/\dead -> x)]
                 {all dead. dead})
          {all dead. dead}
in
\(xs : List data) -> go 5 xs