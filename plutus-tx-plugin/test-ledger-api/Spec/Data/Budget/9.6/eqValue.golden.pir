letrec
  !go : list (pair data data) -> bool
    = \(xs : list (pair data data)) ->
        case
          bool
          xs
          [ (\(hd : pair data data) ->
               case
                 (all dead. list (pair data data) -> bool)
                 (equalsInteger
                    0
                    (unIData (case data hd [(\(l : data) (r : data) -> r)])))
                 [ (/\dead -> \(ds : list (pair data data)) -> False)
                 , (/\dead -> go) ]
                 {all dead. dead})
          , True ]
in
let
  data Unit | Unit_match where
    Unit : Unit
in
letrec
  !rev : all a. list a -> list a -> list a
    = /\a ->
        \(l : list a) (acc : list a) ->
          case
            (Unit -> list a)
            l
            [ (\(x : a) (xs : list a) (ds : Unit) ->
                 rev {a} xs (mkCons {a} x acc))
            , (\(ds : Unit) -> acc) ]
            Unit
in
let
  !unordEqWith :
     (data -> bool) ->
     (data -> data -> bool) ->
     list (pair data data) ->
     list (pair data data) ->
     bool
    = \(is : data -> bool) ->
        letrec
          !go : list (pair data data) -> bool
            = \(xs : list (pair data data)) ->
                case
                  bool
                  xs
                  [ (\(hd : pair data data) ->
                       case
                         (all dead. list (pair data data) -> bool)
                         (is (case data hd [(\(l : data) (r : data) -> r)]))
                         [ (/\dead -> \(ds : list (pair data data)) -> False)
                         , (/\dead -> go) ]
                         {all dead. dead})
                  , True ]
        in
        letrec
          !go : list (pair data data) -> bool
            = \(xs : list (pair data data)) ->
                case
                  bool
                  xs
                  [ (\(hd : pair data data) ->
                       case
                         (all dead. list (pair data data) -> bool)
                         (is (case data hd [(\(l : data) (r : data) -> r)]))
                         [ (/\dead -> \(ds : list (pair data data)) -> False)
                         , (/\dead -> go) ]
                         {all dead. dead})
                  , True ]
        in
        \(eqV : data -> data -> bool) ->
          letrec
            !goBoth :
               list (pair data data) -> list (pair data data) -> bool
              = \(l : list (pair data data))
                 (l : list (pair data data)) ->
                  case
                    (Unit -> bool)
                    l
                    [ (\(x : pair data data) ->
                         let
                           ~v : data
                             = case data x [(\(l : data) (r : data) -> r)]
                         in
                         \(xs : list (pair data data))
                          (ds : Unit) ->
                           case
                             (Unit -> bool)
                             l
                             [ (\(x : pair data data)
                                 (xs : list (pair data data))
                                 (ds : Unit) ->
                                  let
                                    !d : data
                                      = case
                                          data
                                          x
                                          [(\(l : data) (r : data) -> l)]
                                  in
                                  letrec
                                    !goRight :
                                       list (pair data data) ->
                                       list (pair data data) ->
                                       bool
                                      = \(acc : list (pair data data))
                                         (l : list (pair data data)) ->
                                          case
                                            (Unit -> bool)
                                            l
                                            [ (\(x : pair data data)
                                                (xs : list (pair data data))
                                                (ds : Unit) ->
                                                 let
                                                   !v : data
                                                     = case
                                                         data
                                                         x
                                                         [ (\(l : data)
                                                             (r : data) ->
                                                              r) ]
                                                 in
                                                 case
                                                   (all dead. bool)
                                                   (is v)
                                                   [ (/\dead ->
                                                        case
                                                          (all dead. bool)
                                                          (equalsData
                                                             (case
                                                                data
                                                                x
                                                                [ (\(l : data)
                                                                    (r :
                                                                       data) ->
                                                                     l) ])
                                                             d)
                                                          [ (/\dead ->
                                                               goRight
                                                                 (mkCons
                                                                    {pair
                                                                       data
                                                                       data}
                                                                    x
                                                                    acc)
                                                                 xs)
                                                          , (/\dead ->
                                                               case
                                                                 (all dead.
                                                                    bool)
                                                                 (eqV v v)
                                                                 [ (/\dead ->
                                                                      False)
                                                                 , (/\dead ->
                                                                      goBoth
                                                                        xs
                                                                        (rev
                                                                           {pair
                                                                              data
                                                                              data}
                                                                           acc
                                                                           xs)) ]
                                                                 {all dead.
                                                                    dead}) ]
                                                          {all dead. dead})
                                                   , (/\dead ->
                                                        goRight acc xs) ]
                                                   {all dead. dead})
                                            , (\(ds : Unit) -> False) ]
                                            Unit
                                  in
                                  case
                                    (all dead. bool)
                                    (equalsData
                                       d
                                       (case
                                          data
                                          x
                                          [(\(l : data) (r : data) -> l)]))
                                    [ (/\dead ->
                                         case
                                           (all dead. bool)
                                           (is v)
                                           [ (/\dead ->
                                                goRight
                                                  (case
                                                     (all dead.
                                                        list (pair data data))
                                                     (is
                                                        (case
                                                           data
                                                           x
                                                           [ (\(l : data)
                                                               (r : data) ->
                                                                r) ]))
                                                     [ (/\dead ->
                                                          mkCons
                                                            {pair data data}
                                                            x
                                                            [])
                                                     , (/\dead -> []) ]
                                                     {all dead. dead})
                                                  xs)
                                           , (/\dead -> goBoth xs l) ]
                                           {all dead. dead})
                                    , (/\dead ->
                                         case
                                           (all dead. bool)
                                           (eqV
                                              v
                                              (case
                                                 data
                                                 x
                                                 [ (\(l : data) (r : data) ->
                                                      r) ]))
                                           [ (/\dead -> False)
                                           , (/\dead -> goBoth xs xs) ]
                                           {all dead. dead}) ]
                                    {all dead. dead})
                             , (\(ds : Unit) -> go l) ]
                             Unit)
                    , (\(ds : Unit) ->
                         case
                           (Unit -> bool)
                           l
                           [ (\(x : pair data data)
                               (xs : list (pair data data))
                               (ds : Unit) ->
                                go l)
                           , (\(ds : Unit) -> True) ]
                           Unit) ]
                    Unit
          in
          \(eta : list (pair data data)) (eta : list (pair data data)) ->
            goBoth eta eta
in
\(ds :
    (\k a -> list (pair data data))
      bytestring
      ((\k a -> list (pair data data)) bytestring integer))
 (ds :
    (\k a -> list (pair data data))
      bytestring
      ((\k a -> list (pair data data)) bytestring integer)) ->
  unordEqWith
    (\(v : data) -> go (unMapData v))
    (\(v : data) (v : data) ->
       unordEqWith
         (\(v : data) -> equalsInteger 0 (unIData v))
         (\(v : data) (v : data) -> equalsInteger (unIData v) (unIData v))
         (unMapData v)
         (unMapData v))
    ds
    ds