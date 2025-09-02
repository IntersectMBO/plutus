let
  data Unit | Unit_match where
    Unit : Unit
in
\(obsScriptCred : data) (ctx : data) ->
  let
    !ds : (\k a -> list (pair data data)) data integer
      = unMapData
          (headList
             {data}
             (tailList
                {data}
                (tailList
                   {data}
                   (tailList
                      {data}
                      (tailList
                         {data}
                         (tailList
                            {data}
                            (tailList
                               {data}
                               (case
                                  (list data)
                                  (unConstrData
                                     (headList
                                        {data}
                                        (case
                                           (list data)
                                           (unConstrData ctx)
                                           [ (\(l : integer) (r : list data) ->
                                                r) ])))
                                  [ (\(l : integer) (r : list data) ->
                                       r) ]))))))))
    !wdrlAtZero : data
      = case data (headList {pair data data} ds) [(\(l : data) (r : data) -> l)]
    !rest : list (pair data data) = tailList {pair data data} ds
    !wdrlAtOne : data
      = case
          data
          (headList {pair data data} rest)
          [(\(l : data) (r : data) -> l)]
  in
  case
    (all dead. Unit)
    (equalsData obsScriptCred wdrlAtZero)
    [ (/\dead ->
         case
           (all dead. Unit)
           (equalsData obsScriptCred wdrlAtOne)
           [ (/\dead ->
                case
                  (all dead. Unit)
                  ((let
                       a = pair data data
                     in
                     \(p : a -> bool) ->
                       letrec
                         !go : list a -> bool
                           = \(xs : list a) ->
                               case
                                 bool
                                 xs
                                 [ (\(x : a) (xs : list a) ->
                                      case
                                        (all dead. bool)
                                        (p x)
                                        [(/\dead -> go xs), (/\dead -> True)]
                                        {all dead. dead})
                                 , False ]
                       in
                       go)
                     (\(x : pair data data) ->
                        equalsData
                          obsScriptCred
                          (case data x [(\(l : data) (r : data) -> l)]))
                     rest)
                  [ (/\dead ->
                       let
                         !x : Unit = trace {Unit} "not found" Unit
                       in
                       error {Unit})
                  , (/\dead -> Unit) ]
                  {all dead. dead})
           , (/\dead -> Unit) ]
           {all dead. dead})
    , (/\dead -> Unit) ]
    {all dead. dead}