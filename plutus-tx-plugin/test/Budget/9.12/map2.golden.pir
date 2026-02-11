letrec
  data (List :: * -> *) a | List_match where
    Nil : List a
    Cons : a -> List a -> List a
in
let
  data (Tuple :: * -> * -> *) a b | Tuple_match where
    Tuple2 : a -> b -> Tuple a b
in
letrec
  !go : list (pair data data) -> List (Tuple integer integer)
    = \(xs : list (pair data data)) ->
        case
          (List (Tuple integer integer))
          xs
          [ (\(hd : pair data data) (tl : list (pair data data)) ->
               Cons
                 {Tuple integer integer}
                 (Tuple2
                    {integer}
                    {integer}
                    (unIData (case data hd [(\(l : data) (r : data) -> l)]))
                    (unIData (case data hd [(\(l : data) (r : data) -> r)])))
                 (go tl))
          , (Nil {Tuple integer integer}) ]
in
letrec
  !go : list (pair data data) -> list (pair data data) -> list (pair data data)
    = \(acc : list (pair data data)) (xs : list (pair data data)) ->
        case
          (list (pair data data))
          xs
          [(\(hd : pair data data) -> go (mkCons {pair data data} hd acc)), acc]
in
let
  data (Maybe :: * -> *) a | Maybe_match where
    Just : a -> Maybe a
    Nothing : Maybe a
in
letrec
  !goList : List (Tuple data data) -> list (pair data data)
    = \(ds : List (Tuple data data)) ->
        List_match
          {Tuple data data}
          ds
          {list (pair data data)}
          []
          (\(d : Tuple data data) (ds : List (Tuple data data)) ->
             mkCons
               {pair data data}
               (Tuple_match
                  {data}
                  {data}
                  d
                  {pair data data}
                  (\(d : data) (d : data) -> mkPairData d d))
               (goList ds))
in
let
  !unsafeFromSOPList :
     all k a.
       (\a -> a -> data) k ->
       (\a -> a -> data) a ->
       List (Tuple k a) ->
       (\k a -> list (pair data data)) k a
    = /\k a ->
        \(`$dToData` : (\a -> a -> data) k)
         (`$dToData` : (\a -> a -> data) a) ->
          letrec
            !go : List (Tuple k a) -> List (Tuple data data)
              = \(ds : List (Tuple k a)) ->
                  List_match
                    {Tuple k a}
                    ds
                    {all dead. List (Tuple data data)}
                    (/\dead -> Nil {Tuple data data})
                    (\(x : Tuple k a) (xs : List (Tuple k a)) ->
                       /\dead ->
                         Cons
                           {Tuple data data}
                           (Tuple_match
                              {k}
                              {a}
                              x
                              {Tuple data data}
                              (\(k : k) (a : a) ->
                                 Tuple2
                                   {data}
                                   {data}
                                   (`$dToData` k)
                                   (`$dToData` a)))
                           (go xs))
                    {all dead. dead}
          in
          \(eta : List (Tuple k a)) -> goList (go eta)
in
\(n : integer) ->
  let
    !nt : list (pair data data)
      = unsafeFromSOPList
          {integer}
          {integer}
          (\(i : integer) -> iData i)
          (\(i : integer) -> iData i)
          ((let
               a = Tuple integer integer
             in
             \(g : all b. (a -> b -> b) -> b -> b) ->
               g {List a} (\(ds : a) (ds : List a) -> Cons {a} ds ds) (Nil {a}))
             (/\a ->
                \(c : Tuple integer integer -> a -> a) (n : a) ->
                  c
                    (Tuple2 {integer} {integer} (addInteger 3 n) 33)
                    (c
                       (Tuple2 {integer} {integer} (addInteger 4 n) 44)
                       (c
                          (Tuple2 {integer} {integer} (addInteger 6 n) 66)
                          (c
                             (Tuple2 {integer} {integer} (addInteger 7 n) 77)
                             n)))))
  in
  letrec
    !go : list (pair data data) -> list (pair data data)
      = \(xs : list (pair data data)) ->
          case
            (list (pair data data))
            xs
            [ (\(hd : pair data data) (tl : list (pair data data)) ->
                 let
                   !v' : data = case data hd [(\(l : data) (r : data) -> r)]
                   !k' : data = case data hd [(\(l : data) (r : data) -> l)]
                 in
                 letrec
                   !go : list (pair data data) -> Maybe data
                     = \(xs : list (pair data data)) ->
                         case
                           (Maybe data)
                           xs
                           [ (\(hd : pair data data) ->
                                case
                                  (all dead.
                                     list (pair data data) -> Maybe data)
                                  (equalsData
                                     k'
                                     (case
                                        data
                                        hd
                                        [(\(l : data) (r : data) -> l)]))
                                  [ (/\dead -> go)
                                  , (/\dead ->
                                       \(ds : list (pair data data)) ->
                                         Just
                                           {data}
                                           (case
                                              data
                                              hd
                                              [ (\(l : data) (r : data) ->
                                                   r) ])) ]
                                  {all dead. dead})
                           , (Nothing {data}) ]
                 in
                 Maybe_match
                   {data}
                   (go nt)
                   {all dead. list (pair data data)}
                   (\(r : data) ->
                      /\dead ->
                        mkCons
                          {pair data data}
                          (mkPairData
                             k'
                             (iData (addInteger (unIData v') (unIData r))))
                          (go tl))
                   (/\dead ->
                      mkCons {pair data data} (mkPairData k' v') (go tl))
                   {all dead. dead})
            , [] ]
  in
  let
    !nt : list (pair data data)
      = unsafeFromSOPList
          {integer}
          {integer}
          (\(i : integer) -> iData i)
          (\(i : integer) -> iData i)
          ((let
               a = Tuple integer integer
             in
             \(g : all b. (a -> b -> b) -> b -> b) ->
               g {List a} (\(ds : a) (ds : List a) -> Cons {a} ds ds) (Nil {a}))
             (/\a ->
                \(c : Tuple integer integer -> a -> a) (n : a) ->
                  c
                    (Tuple2 {integer} {integer} (addInteger 1 n) 1)
                    (c
                       (Tuple2 {integer} {integer} (addInteger 2 n) 2)
                       (c
                          (Tuple2 {integer} {integer} (addInteger 3 n) 3)
                          (c
                             (Tuple2 {integer} {integer} (addInteger 4 n) 4)
                             (c
                                (Tuple2 {integer} {integer} (addInteger 5 n) 5)
                                n))))))
  in
  letrec
    !go : list (pair data data) -> list (pair data data)
      = \(xs : list (pair data data)) ->
          case
            (list (pair data data))
            xs
            [ (\(hd : pair data data) (tl : list (pair data data)) ->
                 let
                   !tl' : list (pair data data) = go tl
                 in
                 case
                   (all dead. list (pair data data))
                   (let
                     !k : data = case data hd [(\(l : data) (r : data) -> l)]
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
                                    (equalsData
                                       k
                                       (case
                                          data
                                          hd
                                          [(\(l : data) (r : data) -> l)]))
                                    [ (/\dead -> go)
                                    , (/\dead ->
                                         \(ds : list (pair data data)) ->
                                           True) ]
                                    {all dead. dead})
                             , False ]
                   in
                   go nt)
                   [(/\dead -> mkCons {pair data data} hd tl'), (/\dead -> tl')]
                   {all dead. dead})
            , [] ]
  in
  let
    !nt : list (pair data data)
      = let
        !rs' : list (pair data data) = go nt
        !ls' : list (pair data data) = go nt
      in
      go rs' ls'
  in
  go nt