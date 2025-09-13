letrec
  !safeAppend :
     list (pair data data) -> list (pair data data) -> list (pair data data)
    = \(xs : list (pair data data)) (xs : list (pair data data)) ->
        case
          (list (pair data data))
          xs
          [ (\(hd : pair data data) (tl : list (pair data data)) ->
               let
                 !v : data = case data hd [(\(l : data) (r : data) -> r)]
                 !k : data = case data hd [(\(l : data) (r : data) -> l)]
                 !eta : list (pair data data) = safeAppend tl xs
                 !nilCase : list (pair data data)
                   = mkCons {pair data data} (mkPairData k v) []
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
                                     mkCons {pair data data} (mkPairData k v)) ]
                                {all dead. dead})
                         , nilCase ]
               in
               go eta)
          , xs ]
in
let
  !`$dToData` : (\a -> a -> data) integer = \(i : integer) -> iData i
  !`$dToData` : (\a -> a -> data) integer = \(i : integer) -> iData i
  data (These :: * -> * -> *) a b | These_match where
    That : b -> These a b
    These : a -> b -> These a b
    This : a -> These a b
  !`$fToDataThese_$ctoBuiltinData` :
     all a b. (\a -> a -> data) a -> (\a -> a -> data) b -> These a b -> data
    = /\a b ->
        \(`$dToData` : (\a -> a -> data) a)
         (`$dToData` : (\a -> a -> data) b)
         (ds : These a b) ->
          These_match
            {a}
            {b}
            ds
            {data}
            (\(arg : b) -> constrData 1 (mkCons {data} (`$dToData` arg) []))
            (\(arg : a) (arg : b) ->
               constrData
                 2
                 (mkCons
                    {data}
                    (`$dToData` arg)
                    (mkCons {data} (`$dToData` arg) [])))
            (\(arg : a) -> constrData 0 (mkCons {data} (`$dToData` arg) []))
  data (Maybe :: * -> *) a | Maybe_match where
    Just : a -> Maybe a
    Nothing : Maybe a
  !lookup' : data -> list (pair data data) -> Maybe data
    = \(k : data) ->
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
        \(m : list (pair data data)) -> go m
  data (Tuple2 :: * -> * -> *) a b | Tuple2_match where
    Tuple2 : a -> b -> Tuple2 a b
in
letrec
  data (List :: * -> *) a | List_match where
    Nil : List a
    Cons : a -> List a -> List a
in
letrec
  !goList : List (Tuple2 data data) -> list (pair data data)
    = \(ds : List (Tuple2 data data)) ->
        List_match
          {Tuple2 data data}
          ds
          {list (pair data data)}
          []
          (\(d : Tuple2 data data) (ds : List (Tuple2 data data)) ->
             mkCons
               {pair data data}
               (Tuple2_match
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
       List (Tuple2 k a) ->
       (\k a -> list (pair data data)) k a
    = /\k a ->
        \(`$dToData` : (\a -> a -> data) k)
         (`$dToData` : (\a -> a -> data) a) ->
          letrec
            !go : List (Tuple2 k a) -> List (Tuple2 data data)
              = \(ds : List (Tuple2 k a)) ->
                  List_match
                    {Tuple2 k a}
                    ds
                    {all dead. List (Tuple2 data data)}
                    (/\dead -> Nil {Tuple2 data data})
                    (\(x : Tuple2 k a) (xs : List (Tuple2 k a)) ->
                       /\dead ->
                         Cons
                           {Tuple2 data data}
                           (Tuple2_match
                              {k}
                              {a}
                              x
                              {Tuple2 data data}
                              (\(k : k) (a : a) ->
                                 Tuple2
                                   {data}
                                   {data}
                                   (`$dToData` k)
                                   (`$dToData` a)))
                           (go xs))
                    {all dead. dead}
          in
          \(eta : List (Tuple2 k a)) -> goList (go eta)
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
               a = Tuple2 integer integer
             in
             \(g : all b. (a -> b -> b) -> b -> b) ->
               g {List a} (\(ds : a) (ds : List a) -> Cons {a} ds ds) (Nil {a}))
             (/\a ->
                \(c : Tuple2 integer integer -> a -> a) (n : a) ->
                  c
                    (Tuple2 {integer} {integer} (addInteger 3 n) 30)
                    (c
                       (Tuple2 {integer} {integer} (addInteger 4 n) 40)
                       (c
                          (Tuple2 {integer} {integer} (addInteger 6 n) 60)
                          (c
                             (Tuple2 {integer} {integer} (addInteger 7 n) 70)
                             n)))))
  in
  letrec
    !goLeft : list (pair data data) -> list (pair data data)
      = \(xs : list (pair data data)) ->
          case
            (list (pair data data))
            xs
            [ (\(hd : pair data data) (tl : list (pair data data)) ->
                 let
                   !v : data = case data hd [(\(l : data) (r : data) -> r)]
                   !k : data = case data hd [(\(l : data) (r : data) -> l)]
                 in
                 Maybe_match
                   {data}
                   (lookup' k nt)
                   {all dead. list (pair data data)}
                   (\(r : data) ->
                      /\dead ->
                        mkCons
                          {pair data data}
                          (mkPairData
                             k
                             (`$fToDataThese_$ctoBuiltinData`
                                {integer}
                                {integer}
                                `$dToData`
                                `$dToData`
                                (These
                                   {integer}
                                   {integer}
                                   (unIData v)
                                   (unIData r))))
                          (goLeft tl))
                   (/\dead ->
                      mkCons
                        {pair data data}
                        (mkPairData
                           k
                           (`$fToDataThese_$ctoBuiltinData`
                              {integer}
                              {integer}
                              `$dToData`
                              `$dToData`
                              (This {integer} {integer} (unIData v))))
                        (goLeft tl))
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
               a = Tuple2 integer integer
             in
             \(g : all b. (a -> b -> b) -> b -> b) ->
               g {List a} (\(ds : a) (ds : List a) -> Cons {a} ds ds) (Nil {a}))
             (/\a ->
                \(c : Tuple2 integer integer -> a -> a) (n : a) ->
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
    !goRight : list (pair data data) -> list (pair data data)
      = \(xs : list (pair data data)) ->
          case
            (list (pair data data))
            xs
            [ (\(hd : pair data data) (tl : list (pair data data)) ->
                 let
                   !v : data = case data hd [(\(l : data) (r : data) -> r)]
                   !k : data = case data hd [(\(l : data) (r : data) -> l)]
                 in
                 Maybe_match
                   {data}
                   (lookup' k nt)
                   {all dead. list (pair data data)}
                   (\(r : data) ->
                      /\dead ->
                        mkCons
                          {pair data data}
                          (mkPairData
                             k
                             (`$fToDataThese_$ctoBuiltinData`
                                {integer}
                                {integer}
                                `$dToData`
                                `$dToData`
                                (These
                                   {integer}
                                   {integer}
                                   (unIData v)
                                   (unIData r))))
                          (goRight tl))
                   (/\dead ->
                      mkCons
                        {pair data data}
                        (mkPairData
                           k
                           (`$fToDataThese_$ctoBuiltinData`
                              {integer}
                              {integer}
                              `$dToData`
                              `$dToData`
                              (That {integer} {integer} (unIData v))))
                        (goRight tl))
                   {all dead. dead})
            , [] ]
  in
  let
    !nt : list (pair data data) = safeAppend (goLeft nt) (goRight nt)
  in
  (let
      a = Tuple2 integer (These integer integer)
    in
    /\b ->
      \(f : a -> b) ->
        letrec
          !go : List a -> List b
            = \(ds : List a) ->
                List_match
                  {a}
                  ds
                  {all dead. List b}
                  (/\dead -> Nil {b})
                  (\(x : a) (xs : List a) -> /\dead -> Cons {b} (f x) (go xs))
                  {all dead. dead}
        in
        \(eta : List a) -> go eta)
    {Tuple2 integer integer}
    ((let
         a = These integer integer
       in
       /\b ->
         \(f : a -> b) (ds : Tuple2 integer a) ->
           Tuple2_match
             {integer}
             {a}
             ds
             {Tuple2 integer b}
             (\(c : integer) (a : a) -> Tuple2 {integer} {b} c (f a)))
       {integer}
       (\(eta : These integer integer) ->
          These_match
            {integer}
            {integer}
            eta
            {integer}
            (\(b : integer) -> b)
            (\(a : integer) (b : integer) -> addInteger a b)
            (\(a : integer) -> a)))
    ((let
         a = These integer integer
       in
       \(`$dUnsafeFromData` : (\a -> data -> a) integer)
        (`$dUnsafeFromData` : (\a -> data -> a) a) ->
         letrec
           !go : list (pair data data) -> List (Tuple2 integer a)
             = \(xs : list (pair data data)) ->
                 case
                   (List (Tuple2 integer a))
                   xs
                   [ (\(hd : pair data data) (tl : list (pair data data)) ->
                        Cons
                          {Tuple2 integer a}
                          (Tuple2
                             {integer}
                             {a}
                             (`$dUnsafeFromData`
                                (case data hd [(\(l : data) (r : data) -> l)]))
                             (`$dUnsafeFromData`
                                (case data hd [(\(l : data) (r : data) -> r)])))
                          (go tl))
                   , (Nil {Tuple2 integer a}) ]
         in
         \(d : (\k a -> list (pair data data)) integer a) -> go d)
       unIData
       (\(d : data) ->
          (let
              b = list data
            in
            /\r ->
              \(p : pair integer b) (f : integer -> b -> r) -> case r p [f])
            {These integer integer}
            (unConstrData d)
            (\(index : integer) (args : list data) ->
               case
                 (list data -> These integer integer)
                 index
                 [ (\(ds : list data) ->
                      This {integer} {integer} (unIData (headList {data} ds)))
                 , (\(ds : list data) ->
                      That {integer} {integer} (unIData (headList {data} ds)))
                 , (\(ds : list data) ->
                      These
                        {integer}
                        {integer}
                        (unIData (headList {data} ds))
                        (unIData (headList {data} (tailList {data} ds)))) ]
                 args))
       nt)