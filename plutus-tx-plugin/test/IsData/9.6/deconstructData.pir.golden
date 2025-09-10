let
  data Unit | Unit_match where
    Unit : Unit
  data (Tuple2 :: * -> * -> *) a b | Tuple2_match where
    Tuple2 : a -> b -> Tuple2 a b
  !caseList' : all a r. r -> (a -> list a -> r) -> list a -> r
    = /\a r -> \(z : r) (f : a -> list a -> r) (xs : list a) -> case r xs [f, z]
  !casePair : all a b r. pair a b -> (a -> b -> r) -> r
    = /\a b r -> \(p : pair a b) (f : a -> b -> r) -> case r p [f]
  !chooseData : all a. data -> a -> a -> a -> a -> a -> a = chooseData
  !equalsInteger : integer -> integer -> bool = equalsInteger
  data (Maybe :: * -> *) a | Maybe_match where
    Just : a -> Maybe a
    Nothing : Maybe a
  !unsafeDataAsConstr : data -> pair integer (list data) = unConstrData
  ~`$fFromDataTuple2_$cfromBuiltinData` :
     all a b.
       (\a -> data -> Maybe a) a ->
       (\a -> data -> Maybe a) b ->
       data ->
       Maybe (Tuple2 a b)
    = /\a b ->
        \(`$dFromData` : (\a -> data -> Maybe a) a)
         (`$dFromData` : (\a -> data -> Maybe a) b)
         (d : data) ->
          let
            !d : data = d
          in
          chooseData
            {Unit -> Maybe (Tuple2 a b)}
            d
            (\(ds : Unit) ->
               casePair
                 {integer}
                 {list data}
                 {Maybe (Tuple2 a b)}
                 (unsafeDataAsConstr d)
                 (\(l : integer) ->
                    let
                      !l : integer = l
                    in
                    \(r : list data) ->
                      let
                        !r : list data = r
                      in
                      case
                        (all dead. Maybe (Tuple2 a b))
                        (equalsInteger 0 l)
                        [ (/\dead -> Nothing {Tuple2 a b})
                        , (/\dead ->
                             Maybe_match
                               {Tuple2 data (list data)}
                               (caseList'
                                  {data}
                                  {Maybe (Tuple2 data (list data))}
                                  (Nothing {Tuple2 data (list data)})
                                  (\(h : data) ->
                                     let
                                       !h : data = h
                                     in
                                     \(t : list data) ->
                                       let
                                         !t : list data = t
                                       in
                                       Just
                                         {Tuple2 data (list data)}
                                         (Tuple2 {data} {list data} h t))
                                  r)
                               {all dead. Maybe (Tuple2 a b)}
                               (\(ds : Tuple2 data (list data)) ->
                                  /\dead ->
                                    Tuple2_match
                                      {data}
                                      {list data}
                                      ds
                                      {Maybe (Tuple2 a b)}
                                      (\(ds : data) (ds : list data) ->
                                         Maybe_match
                                           {a}
                                           (`$dFromData` ds)
                                           {all dead. Maybe (Tuple2 a b)}
                                           (\(arg : a) ->
                                              /\dead ->
                                                Maybe_match
                                                  {data}
                                                  (caseList'
                                                     {data}
                                                     {Maybe data}
                                                     (Nothing {data})
                                                     (\(h : data) ->
                                                        let
                                                          !h : data = h
                                                        in
                                                        \(ds : list data) ->
                                                          Just {data} h)
                                                     ds)
                                                  {all dead. Maybe (Tuple2 a b)}
                                                  (\(ds : data) ->
                                                     /\dead ->
                                                       Maybe_match
                                                         {b}
                                                         (`$dFromData` ds)
                                                         {all dead.
                                                            Maybe (Tuple2 a b)}
                                                         (\(arg : b) ->
                                                            /\dead ->
                                                              Just
                                                                {Tuple2 a b}
                                                                (Tuple2
                                                                   {a}
                                                                   {b}
                                                                   arg
                                                                   arg))
                                                         (/\dead ->
                                                            Nothing
                                                              {Tuple2 a b})
                                                         {all dead. dead})
                                                  (/\dead ->
                                                     Nothing {Tuple2 a b})
                                                  {all dead. dead})
                                           (/\dead -> Nothing {Tuple2 a b})
                                           {all dead. dead}))
                               (/\dead -> Nothing {Tuple2 a b})
                               {all dead. dead}) ]
                        {all dead. dead}))
            (\(ds : Unit) -> Nothing {Tuple2 a b})
            (\(ds : Unit) -> Nothing {Tuple2 a b})
            (\(ds : Unit) -> Nothing {Tuple2 a b})
            (\(ds : Unit) -> Nothing {Tuple2 a b})
            Unit
  ~`$fFromDataTuple2` :
     all a b.
       (\a -> data -> Maybe a) a ->
       (\a -> data -> Maybe a) b ->
       (\a -> data -> Maybe a) (Tuple2 a b)
    = `$fFromDataTuple2_$cfromBuiltinData`
  !unsafeDataAsB : data -> bytestring = unBData
  !unsafeDataAsI : data -> integer = unIData
  !unsafeDataAsList : data -> list data = unListData
  !unsafeDataAsMap : data -> list (pair data data) = unMapData
  ~`$fFromDataInteger_$cfromBuiltinData` : data -> Maybe integer
    = \(d : data) ->
        let
          !d : data = d
        in
        chooseData
          {Unit -> Maybe integer}
          d
          (\(ds : Unit) ->
             casePair
               {integer}
               {list data}
               {Maybe integer}
               (unsafeDataAsConstr d)
               (\(l : integer) (r : list data) -> Nothing {integer}))
          (\(ds : Unit) ->
             let
               !ds : list (pair data data) = unsafeDataAsMap d
             in
             Nothing {integer})
          (\(ds : Unit) ->
             let
               !ds : list data = unsafeDataAsList d
             in
             Nothing {integer})
          (\(ds : Unit) -> Just {integer} (unsafeDataAsI d))
          (\(ds : Unit) ->
             let
               !ds : bytestring = unsafeDataAsB d
             in
             Nothing {integer})
          Unit
  ~`$fFromDataInteger` : (\a -> data -> Maybe a) integer
    = `$fFromDataInteger_$cfromBuiltinData`
  ~`$dFromData` : (\a -> data -> Maybe a) (Tuple2 integer integer)
    = `$fFromDataTuple2`
        {integer}
        {integer}
        `$fFromDataInteger`
        `$fFromDataInteger`
  ~fromBuiltinData : all a. (\a -> data -> Maybe a) a -> data -> Maybe a
    = /\a -> \(v : (\a -> data -> Maybe a) a) -> v
in
\(ds : data) ->
  let
    !ds : data = ds
  in
  fromBuiltinData {Tuple2 integer integer} `$dFromData` ds