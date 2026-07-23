let
  data (Maybe :: * -> *) a | Maybe_match where
    Just : a -> Maybe a
    Nothing : Maybe a
  data Unit | Unit_match where
    Unit : Unit
in
\(d : data) ->
  case
    (all dead. unit)
    (case
       bool
       (case
          (list data)
          (unConstrData d)
          [(\(l : integer) (r : list data) -> r)])
       [ (\(ds : data) (ds : list data) ->
            case
              bool
              ds
              [ (\(ds : data) (ds : list data) ->
                   let
                     !tup : pair integer (list data)
                       = unConstrData (headList {data} ds)
                   in
                   case
                     (all dead. bool)
                     (equalsInteger
                        1
                        ((let
                             b = list data
                           in
                           \(x : pair integer b) ->
                             case integer x [(\(l : integer) (r : b) -> l)])
                           tup))
                     [ (/\dead -> False)
                     , (/\dead ->
                          case
                            bool
                            (case
                               (list data)
                               tup
                               [(\(l : integer) (r : list data) -> r)])
                            [ (\(ds : data) (ds : list data) ->
                                 Maybe_match
                                   {data}
                                   ((let
                                        b = list data
                                      in
                                      /\r ->
                                        \(p : pair integer b)
                                         (f : integer -> b -> r) ->
                                          case r p [f])
                                      {Maybe data}
                                      (unConstrData (headList {data} ds))
                                      (\(index : integer) (args : list data) ->
                                         case
                                           (list data -> Maybe data)
                                           index
                                           [ (\(ds : list data) ->
                                                Just
                                                  {data}
                                                  (headList {data} ds))
                                           , (\(ds : list data) ->
                                                Nothing {data}) ]
                                           args))
                                   {all dead. bool}
                                   (\(ds : data) -> /\dead -> True)
                                   (/\dead -> False)
                                   {all dead. dead}) ]) ]
                     {all dead. dead}) ]) ])
    [ (/\dead -> let !x : Unit = trace {Unit} "PT5" Unit in error {unit})
    , (/\dead -> ()) ]
    {all dead. dead}