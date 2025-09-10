let
  data (Tuple3 :: * -> * -> * -> *) a b c | Tuple3_match where
    Tuple3 : a -> b -> c -> Tuple3 a b c
  data (Either :: * -> * -> *) a b | Either_match where
    Left : a -> Either a b
    Right : b -> Either a b
  data (Maybe :: * -> *) a | Maybe_match where
    Just : a -> Maybe a
    Nothing : Maybe a
  !casePair : all a b r. pair a b -> (a -> b -> r) -> r
    = /\a b r -> \(p : pair a b) (f : a -> b -> r) -> case r p [f]
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
    casePair
      {integer}
      {list data}
      {Either integer b}
      (unConstrData d)
      (\(index : integer) (args : list data) ->
         case
           (list data -> Either integer b)
           index
           [ (\(ds : list data) ->
                Left {integer} {b} (`$dUnsafeFromData` (headList {data} ds)))
           , (\(ds : list data) ->
                Right {integer} {b} (`$dUnsafeFromData` (headList {data} ds))) ]
           args))
  unIData
  ((let
       a = Tuple3 bool integer bool
     in
     \(`$dUnsafeFromData` : (\a -> data -> a) a) (d : data) ->
       casePair
         {integer}
         {list data}
         {Maybe a}
         (unConstrData d)
         (\(index : integer) (args : list data) ->
            case
              (list data -> Maybe a)
              index
              [ (\(ds : list data) ->
                   Just {a} (`$dUnsafeFromData` (headList {data} ds)))
              , (\(ds : list data) -> Nothing {a}) ]
              args))
     (\(d : data) ->
        casePair
          {integer}
          {list data}
          {Tuple3 bool integer bool}
          (unConstrData d)
          (\(index : integer) (args : list data) ->
             case
               (list data -> Tuple3 bool integer bool)
               index
               [ (\(ds : list data) ->
                    let
                      !l : list data = tailList {data} ds
                    in
                    Tuple3
                      {bool}
                      {integer}
                      {bool}
                      (let
                        !d : data = headList {data} ds
                      in
                      casePair
                        {integer}
                        {list data}
                        {bool}
                        (unConstrData d)
                        (\(index : integer) (args : list data) ->
                           case
                             (list data -> bool)
                             index
                             [ (\(ds : list data) -> False)
                             , (\(ds : list data) -> True) ]
                             args))
                      (unIData (headList {data} l))
                      (let
                        !d : data = headList {data} (tailList {data} l)
                      in
                      casePair
                        {integer}
                        {list data}
                        {bool}
                        (unConstrData d)
                        (\(index : integer) (args : list data) ->
                           case
                             (list data -> bool)
                             index
                             [ (\(ds : list data) -> False)
                             , (\(ds : list data) -> True) ]
                             args))) ]
               args)))
  d