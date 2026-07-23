(letrec
    !go : list data -> integer
      = \(xs : list data) ->
          case
            integer
            xs
            [(\(ds : data) (eta : list data) -> addInteger 1 (go eta)), 0]
  in
  let
    data Unit | Unit_match where
      Unit : Unit
  in
  \(d : data) ->
    case
      Unit
      (case
         (list data)
         (unConstrData d)
         [(\(l : integer) (r : list data) -> r)])
      [ (\(ds : data)
          (ds : list data) ->
           case
             (all dead. Unit)
             (equalsInteger
                0
                (modInteger
                   (let
                     !ds :
                        (\a -> list data) data
                       = (let
                             r = (\a -> list data) data
                           in
                           \(scrut : data)
                            (cont :
                               (\a -> list data) data ->
                               (\a -> list data) data ->
                               (\a -> list data) data ->
                               (\k a -> list (pair data data))
                                 bytestring
                                 ((\k a -> list (pair data data))
                                    bytestring
                                    integer) ->
                               (\k a -> list (pair data data))
                                 bytestring
                                 ((\k a -> list (pair data data))
                                    bytestring
                                    integer) ->
                               (\a -> list data) data ->
                               (\k a -> list (pair data data)) data integer ->
                               (\a -> data) integer ->
                               (\a -> list data) bytestring ->
                               (\k a -> list (pair data data)) data data ->
                               (\k a -> list (pair data data))
                                 bytestring
                                 data ->
                               bytestring ->
                               r)
                            (fail : unit -> r) ->
                             case
                               r
                               (case
                                  (list data)
                                  (unConstrData scrut)
                                  [(\(l : integer) (r : list data) -> r)])
                               [ (\(ds : data)
                                   (ds : list data) ->
                                    case
                                      r
                                      ds
                                      [ (\(ds : data)
                                          (ds : list data) ->
                                           case
                                             r
                                             ds
                                             [ (\(ds : data)
                                                 (ds : list data) ->
                                                  case
                                                    r
                                                    ds
                                                    [ (\(ds : data)
                                                        (ds : list data) ->
                                                         case
                                                           r
                                                           ds
                                                           [ (\(ds : data)
                                                               (ds :
                                                                  list data) ->
                                                                case
                                                                  r
                                                                  ds
                                                                  [ (\(ds :
                                                                         data)
                                                                      (ds :
                                                                         list
                                                                           data) ->
                                                                       case
                                                                         r
                                                                         ds
                                                                         [ (\(ds :
                                                                                data)
                                                                             (ds :
                                                                                list
                                                                                  data) ->
                                                                              case
                                                                                r
                                                                                ds
                                                                                [ (\(ds :
                                                                                       data)
                                                                                    (ds :
                                                                                       list
                                                                                         data) ->
                                                                                     case
                                                                                       r
                                                                                       ds
                                                                                       [ (\(ds :
                                                                                              data)
                                                                                           (ds :
                                                                                              list
                                                                                                data) ->
                                                                                            case
                                                                                              r
                                                                                              ds
                                                                                              [ (\(ds :
                                                                                                     data)
                                                                                                  (ds :
                                                                                                     list
                                                                                                       data) ->
                                                                                                   case
                                                                                                     r
                                                                                                     ds
                                                                                                     [ (\(ds :
                                                                                                            data)
                                                                                                         (ds :
                                                                                                            list
                                                                                                              data) ->
                                                                                                          cont
                                                                                                            (unListData
                                                                                                               ds)
                                                                                                            (unListData
                                                                                                               ds)
                                                                                                            (unListData
                                                                                                               ds)
                                                                                                            (unMapData
                                                                                                               ds)
                                                                                                            (unMapData
                                                                                                               ds)
                                                                                                            (unListData
                                                                                                               ds)
                                                                                                            (unMapData
                                                                                                               ds)
                                                                                                            ds
                                                                                                            (unListData
                                                                                                               ds)
                                                                                                            (unMapData
                                                                                                               ds)
                                                                                                            (unMapData
                                                                                                               ds)
                                                                                                            (let
                                                                                                              !d :
                                                                                                                 data
                                                                                                                = headList
                                                                                                                    {data}
                                                                                                                    ds
                                                                                                            in
                                                                                                            (let
                                                                                                                b
                                                                                                                  = list
                                                                                                                      data
                                                                                                              in
                                                                                                              /\r ->
                                                                                                                \(p :
                                                                                                                    pair
                                                                                                                      integer
                                                                                                                      b)
                                                                                                                 (f :
                                                                                                                    integer ->
                                                                                                                    b ->
                                                                                                                    r) ->
                                                                                                                  case
                                                                                                                    r
                                                                                                                    p
                                                                                                                    [ f ])
                                                                                                              {bytestring}
                                                                                                              (unConstrData
                                                                                                                 d)
                                                                                                              (\(index :
                                                                                                                   integer)
                                                                                                                (args :
                                                                                                                   list
                                                                                                                     data) ->
                                                                                                                 case
                                                                                                                   (list
                                                                                                                      data ->
                                                                                                                    bytestring)
                                                                                                                   index
                                                                                                                   [ (\(ds :
                                                                                                                          list
                                                                                                                            data) ->
                                                                                                                        unBData
                                                                                                                          (headList
                                                                                                                             {data}
                                                                                                                             ds)) ]
                                                                                                                   args))) ]) ]) ]) ]) ]) ]) ]) ]) ]) ]) ])
                           ds
                           (\(ds : (\a -> list data) data)
                             (ds : (\a -> list data) data)
                             (ds : (\a -> list data) data)
                             (ds :
                                (\k a -> list (pair data data))
                                  bytestring
                                  ((\k a -> list (pair data data))
                                     bytestring
                                     integer))
                             (ds :
                                (\k a -> list (pair data data))
                                  bytestring
                                  ((\k a -> list (pair data data))
                                     bytestring
                                     integer))
                             (ds : (\a -> list data) data)
                             (ds : (\k a -> list (pair data data)) data integer)
                             (ds : (\a -> data) integer)
                             (ds : (\a -> list data) bytestring)
                             (ds : (\k a -> list (pair data data)) data data)
                             (ds :
                                (\k a -> list (pair data data)) bytestring data)
                             (ds : bytestring) ->
                              ds)
                           (\(void : unit) -> error {(\a -> list data) data})
                   in
                   go ds)
                   2))
             [ (/\dead ->
                  let
                    !x : Unit = trace {Unit} "Odd number of outputs" Unit
                  in
                  error {Unit})
             , (/\dead -> Unit) ]
             {all dead. dead}) ])
  (Constr 0
     [ Constr 0
         [ List []
         , List []
         , List
             [ Constr 0
                 [ Constr 0 [Constr 0 [B #], Constr 1 []]
                 , Map [(B #, Map [(B #, I 1)])]
                 , Constr 0 []
                 , Constr 1 [] ] ]
         , Map []
         , Map []
         , List []
         , Map []
         , Constr 0
             [ Constr 0 [Constr 0 [], Constr 1 []]
             , Constr 0 [Constr 2 [], Constr 1 []] ]
         , List []
         , Map []
         , Map []
         , Constr 0 [B #] ]
     , Constr 1 [Constr 0 [Constr 0 [B #], I 0]] ])