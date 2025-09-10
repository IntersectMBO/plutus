let
  data Unit | Unit_match where
    Unit : Unit
in
\(r_stake_cred : data) ->
  letrec
    !lookForCred : list (pair data data) -> Unit
      = \(l : list (pair data data)) ->
          (let
              a = pair data data
            in
            /\r ->
              \(z : r) (f : a -> list a -> r) (xs : list a) -> case r xs [f, z])
            {Unit -> Unit}
            (\(ds : Unit) ->
               let
                 !x : Unit = trace {Unit} "not found" Unit
               in
               error {Unit})
            (\(x : pair data data) (xs : list (pair data data)) (ds : Unit) ->
               case
                 (all dead. Unit)
                 (equalsData
                    r_stake_cred
                    (case data x [(\(l : data) (r : data) -> l)]))
                 [(/\dead -> lookForCred xs), (/\dead -> Unit)]
                 {all dead. dead})
            l
            Unit
  in
  \(r_ctx : data) ->
    let
      !wdrl : list (pair data data)
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
                                             (unConstrData r_ctx)
                                             [ (\(l : integer)
                                                 (r : list data) ->
                                                  r) ])))
                                    [ (\(l : integer) (r : list data) ->
                                         r) ]))))))))
      !wdrlAtZero : data
        = case
            data
            (headList {pair data data} wdrl)
            [(\(l : data) (r : data) -> l)]
      !rest : list (pair data data) = tailList {pair data data} wdrl
      !wdrlAtOne : data
        = case
            data
            (headList {pair data data} rest)
            [(\(l : data) (r : data) -> l)]
    in
    case
      (all dead. Unit)
      (equalsData r_stake_cred wdrlAtZero)
      [ (/\dead ->
           case
             (all dead. Unit)
             (equalsData r_stake_cred wdrlAtOne)
             [(/\dead -> lookForCred rest), (/\dead -> Unit)]
             {all dead. dead})
      , (/\dead -> Unit) ]
      {all dead. dead}