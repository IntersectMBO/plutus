let
  data (Tuple3 :: * -> * -> * -> *) a b c | Tuple3_match where
    Tuple3 : a -> b -> c -> Tuple3 a b c
  data (Either :: * -> * -> *) a b | Either_match where
    Left : a -> Either a b
    Right : b -> Either a b
  data (Maybe :: * -> *) a | Maybe_match where
    Just : a -> Maybe a
    Nothing : Maybe a
  !d : data
    = (let
          b = Maybe (Tuple3 bool integer bool)
        in
        \(`$dToData` : (\a -> a -> data) integer)
         (`$dToData` : (\a -> a -> data) b)
         (ds : Either integer b) ->
          Either_match
            {integer}
            {b}
            ds
            {data}
            (\(arg : integer) ->
               constrData 0 (mkCons {data} (`$dToData` arg) []))
            (\(arg : b) -> constrData 1 (mkCons {data} (`$dToData` arg) [])))
        (\(i : integer) -> iData i)
        ((let
             a = Tuple3 bool integer bool
           in
           \(`$dToData` : (\a -> a -> data) a) (ds : Maybe a) ->
             Maybe_match
               {a}
               ds
               {all dead. data}
               (\(arg : a) ->
                  /\dead -> constrData 0 (mkCons {data} (`$dToData` arg) []))
               (/\dead -> Constr 1 [])
               {all dead. dead})
           (\(ds : Tuple3 bool integer bool) ->
              Tuple3_match
                {bool}
                {integer}
                {bool}
                ds
                {data}
                (\(arg : bool) (arg : integer) (arg : bool) ->
                   constrData
                     0
                     (mkCons
                        {data}
                        (case
                           (all dead. data)
                           arg
                           [(/\dead -> Constr 0 []), (/\dead -> Constr 1 [])]
                           {all dead. dead})
                        (mkCons
                           {data}
                           (iData arg)
                           (mkCons
                              {data}
                              (case
                                 (all dead. data)
                                 arg
                                 [ (/\dead -> Constr 0 [])
                                 , (/\dead -> Constr 1 []) ]
                                 {all dead. dead})
                              []))))))
        (Right
           {integer}
           {Maybe (Tuple3 bool integer bool)}
           (Just
              {Tuple3 bool integer bool}
              (Tuple3 {bool} {integer} {bool} True 1 False)))
in
(let
    b = Maybe (Tuple3 bool integer bool)
  in
  \(`$dUnsafeFromData` : (\a -> data -> a) integer)
   (`$dUnsafeFromData` : (\a -> data -> a) b)
   (d : data) ->
    case
      (Either integer b)
      d
      [ (\(ds : list data) ->
           Left {integer} {b} (`$dUnsafeFromData` (headList {data} ds)))
      , (\(ds : list data) ->
           Right {integer} {b} (`$dUnsafeFromData` (headList {data} ds))) ])
  unIData
  ((let
       a = Tuple3 bool integer bool
     in
     \(`$dUnsafeFromData` : (\a -> data -> a) a) (d : data) ->
       case
         (Maybe a)
         d
         [ (\(ds : list data) ->
              Just {a} (`$dUnsafeFromData` (headList {data} ds)))
         , (\(ds : list data) -> Nothing {a}) ])
     (\(d : data) ->
        case
          (Tuple3 bool integer bool)
          d
          [ (\(ds : list data) ->
               case
                 (Tuple3 bool integer bool)
                 ds
                 [ (\(ds : data) (ds : list data) ->
                      case
                        (Tuple3 bool integer bool)
                        ds
                        [ (\(ds : data) (ds : list data) ->
                             Tuple3
                               {bool}
                               {integer}
                               {bool}
                               (case
                                  bool
                                  ds
                                  [ (\(ds : list data) -> False)
                                  , (\(ds : list data) -> True) ])
                               (unIData ds)
                               (case
                                  bool
                                  (headList {data} ds)
                                  [ (\(ds : list data) -> False)
                                  , (\(ds : list data) -> True) ])) ]) ]) ]))
  d