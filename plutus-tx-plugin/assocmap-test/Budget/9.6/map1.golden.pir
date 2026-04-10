letrec
  data (List :: * -> *) a | List_match where
    Nil : List a
    Cons : a -> List a -> List a
in
letrec
  !`$dmenumFromTo_$cenumFromTo` : integer -> integer -> List integer
    = \(x : integer) (lim : integer) ->
        case
          (all dead. List integer)
          (case bool (lessThanEqualsInteger x lim) [True, False])
          [ (/\dead ->
               Cons
                 {integer}
                 x
                 (`$dmenumFromTo_$cenumFromTo` (addInteger 1 x) lim))
          , (/\dead -> Nil {integer}) ]
          {all dead. dead}
in
let
  data (Tuple5 :: * -> * -> * -> * -> * -> *) a b c d e | Tuple5_match where
    Tuple5 : a -> b -> c -> d -> e -> Tuple5 a b c d e
  data (Maybe :: * -> *) a | Maybe_match where
    Just : a -> Maybe a
    Nothing : Maybe a
  !lookup :
     all k a.
       (\a -> a -> data) k ->
       (\a -> data -> a) a ->
       k ->
       (\k a -> list (pair data data)) k a ->
       Maybe a
    = /\k a ->
        \(`$dToData` : (\a -> a -> data) k)
         (`$dUnsafeFromData` : (\a -> data -> a) a)
         (ds : k)
         (ds : (\k a -> list (pair data data)) k a) ->
          Maybe_match
            {data}
            (let
              !k : data = `$dToData` ds
            in
            letrec
              !go : list (pair data data) -> Maybe data
                = \(xs : list (pair data data)) ->
                    case
                      (Maybe data)
                      xs
                      [ (\(hd : pair data data) ->
                           case
                             (all dead. list (pair data data) -> Maybe data)
                             (equalsData
                                k
                                (case data hd [(\(l : data) (r : data) -> l)]))
                             [ (/\dead -> go)
                             , (/\dead ->
                                  \(ds : list (pair data data)) ->
                                    Just
                                      {data}
                                      (case
                                         data
                                         hd
                                         [(\(l : data) (r : data) -> r)])) ]
                             {all dead. dead})
                      , (Nothing {data}) ]
            in
            go ds)
            {all dead. Maybe a}
            (\(a : data) -> /\dead -> Just {a} (`$dUnsafeFromData` a))
            (/\dead -> Nothing {a})
            {all dead. dead}
in
\(n : integer) ->
  let
    !nt : list (pair data data)
      = (let
            b = (\k a -> list (pair data data)) integer integer
          in
          \(k : integer -> b -> b) (z : b) ->
            letrec
              !go : List integer -> b
                = \(ds : List integer) ->
                    List_match
                      {integer}
                      ds
                      {all dead. b}
                      (/\dead -> z)
                      (\(y : integer) (ys : List integer) ->
                         /\dead -> k y (go ys))
                      {all dead. dead}
            in
            \(eta : List integer) -> go eta)
          (\(i : integer) ->
             let
               !ds : integer = addInteger n i
             in
             \(ds : (\k a -> list (pair data data)) integer integer) ->
               let
                 !k : data = iData ds
                 !a : data = iData i
                 !nilCase : list (pair data data)
                   = mkCons {pair data data} (mkPairData k a) []
               in
               letrec
                 !go : list (pair data data) -> list (pair data data)
                   = \(xs : list (pair data data)) ->
                       case
                         (list (pair data data))
                         xs
                         [ (\(hd : pair data data) ->
                              case
                                (all dead.
                                   list (pair data data) ->
                                   list (pair data data))
                                (equalsData
                                   k
                                   (case
                                      data
                                      hd
                                      [(\(l : data) (r : data) -> l)]))
                                [ (/\dead ->
                                     \(eta : list (pair data data)) ->
                                       mkCons {pair data data} hd (go eta))
                                , (/\dead ->
                                     mkCons {pair data data} (mkPairData k a)) ]
                                {all dead. dead})
                         , nilCase ]
               in
               go ds)
          (mkCons {pair data data} (mkPairData (iData n) (I 0)) [])
          (`$dmenumFromTo_$cenumFromTo` 1 10)
    !nt : list (pair data data)
      = (let
            !k : data = iData (addInteger 5 n)
          in
          letrec
            !go : list (pair data data) -> list (pair data data)
              = \(xs : list (pair data data)) ->
                  case
                    (list (pair data data))
                    xs
                    [ (\(hd : pair data data) ->
                         case
                           (all dead.
                              list (pair data data) -> list (pair data data))
                           (equalsData
                              k
                              (case data hd [(\(l : data) (r : data) -> l)]))
                           [ (/\dead ->
                                \(eta : list (pair data data)) ->
                                  mkCons {pair data data} hd (go eta))
                           , (/\dead -> \(x : list (pair data data)) -> x) ]
                           {all dead. dead})
                    , [] ]
          in
          go)
          nt
  in
  Tuple5
    {Maybe integer}
    {Maybe integer}
    {Maybe integer}
    {Maybe integer}
    {Maybe integer}
    (lookup {integer} {integer} (\(i : integer) -> iData i) unIData n nt)
    (lookup
       {integer}
       {integer}
       (\(i : integer) -> iData i)
       unIData
       (addInteger 5 n)
       nt)
    (lookup
       {integer}
       {integer}
       (\(i : integer) -> iData i)
       unIData
       (addInteger 10 n)
       nt)
    (lookup
       {integer}
       {integer}
       (\(i : integer) -> iData i)
       unIData
       (addInteger 20 n)
       nt)
    (lookup
       {integer}
       {integer}
       (\(i : integer) -> iData i)
       unIData
       (addInteger 5 n)
       nt)