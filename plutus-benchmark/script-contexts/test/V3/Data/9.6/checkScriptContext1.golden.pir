(letrec
    !go : list data -> integer
      = \(xs : list data) ->
          case
            integer
            xs
            [(\(ds : data) (eta : list data) -> addInteger 1 (go eta)), 0]
  in
  let
    data (Maybe :: * -> *) a | Maybe_match where
      Just : a -> Maybe a
      Nothing : Maybe a
    !`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData` :
       all a. (\a -> data -> a) a -> data -> Maybe a
      = /\a ->
          \(`$dUnsafeFromData` : (\a -> data -> a) a) (d : data) ->
            (let
                b = list data
              in
              /\r ->
                \(p : pair integer b) (f : integer -> b -> r) -> case r p [f])
              {Maybe a}
              (unConstrData d)
              (\(index : integer) (args : list data) ->
                 case
                   (list data -> Maybe a)
                   index
                   [ (\(ds : list data) ->
                        Just {a} (`$dUnsafeFromData` (headList {data} ds)))
                   , (\(ds : list data) -> Nothing {a}) ]
                   args)
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
                               integer ->
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
                               (\k a -> list (pair data data))
                                 data
                                 ((\k a -> list (pair data data)) data data) ->
                               (\a -> list data) data ->
                               Maybe integer ->
                               Maybe integer ->
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
                                                                                                                                        (unIData
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
                                                                                                                                        (unBData
                                                                                                                                           ds)
                                                                                                                                        (unMapData
                                                                                                                                           ds)
                                                                                                                                        (unListData
                                                                                                                                           ds)
                                                                                                                                        (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                                                                                                                                           {integer}
                                                                                                                                           unIData
                                                                                                                                           ds)
                                                                                                                                        (`$fUnsafeFromDataMaybe_$cunsafeFromBuiltinData`
                                                                                                                                           {integer}
                                                                                                                                           unIData
                                                                                                                                           (headList
                                                                                                                                              {data}
                                                                                                                                              ds))) ]) ]) ]) ]) ]) ]) ]) ]) ]) ]) ]) ]) ]) ]) ])
                           ds
                           (\(ds : (\a -> list data) data)
                             (ds : (\a -> list data) data)
                             (ds : (\a -> list data) data)
                             (ds : integer)
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
                             (ds : bytestring)
                             (ds :
                                (\k a -> list (pair data data))
                                  data
                                  ((\k a -> list (pair data data)) data data))
                             (ds : (\a -> list data) data)
                             (ds : Maybe integer)
                             (ds : Maybe integer) ->
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
         , I 10000
         , Map []
         , List []
         , Map []
         , Constr 0
             [ Constr 0 [Constr 0 [], Constr 1 []]
             , Constr 0 [Constr 2 [], Constr 1 []] ]
         , List []
         , Map []
         , Map []
         , B #
         , Map []
         , List []
         , Constr 1 []
         , Constr 1 [] ]
     , I 1
     , Constr 1 [Constr 0 [B #, I 0], Constr 1 []] ])