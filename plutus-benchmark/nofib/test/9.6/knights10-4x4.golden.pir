(let
    data (Maybe :: * -> *) a | Maybe_match where
      Just : a -> Maybe a
      Nothing : Maybe a
    data (Tuple2 :: * -> * -> *) a b | Tuple2_match where
      Tuple2 : a -> b -> Tuple2 a b
  in
  letrec
    data (List :: * -> *) a | List_match where
      Nil : List a
      Cons : a -> List a -> List a
  in
  let
    data ChessSet | ChessSet_match where
      Board :
        integer ->
        integer ->
        Maybe (Tuple2 integer integer) ->
        List (Tuple2 integer integer) ->
        ChessSet
    !`$fEqChessSet_$c==` : ChessSet -> ChessSet -> bool
      = \(ds : ChessSet) (ds : ChessSet) -> True
    data Ordering | Ordering_match where
      EQ : Ordering
      GT : Ordering
      LT : Ordering
    data (Ord :: * -> *) a | Ord_match where
      CConsOrd :
        (\a -> a -> a -> bool) a ->
        (a -> a -> Ordering) ->
        (a -> a -> bool) ->
        (a -> a -> bool) ->
        (a -> a -> bool) ->
        (a -> a -> bool) ->
        (a -> a -> a) ->
        (a -> a -> a) ->
        Ord a
    !v : Ord ChessSet
      = CConsOrd
          {ChessSet}
          `$fEqChessSet_$c==`
          (\(eta : ChessSet) (eta : ChessSet) -> EQ)
          (\(x : ChessSet) (y : ChessSet) -> False)
          `$fEqChessSet_$c==`
          (\(x : ChessSet) (y : ChessSet) -> False)
          `$fEqChessSet_$c==`
          (\(x : ChessSet) (y : ChessSet) -> y)
          (\(x : ChessSet) (y : ChessSet) -> x)
    !ifThenElse : all a. bool -> a -> a -> a
      = /\a -> \(b : bool) (x : a) (y : a) -> case a b [y, x]
    !v : Ord integer
      = CConsOrd
          {integer}
          (\(x : integer) (y : integer) -> equalsInteger x y)
          (\(eta : integer) (eta : integer) ->
             case
               (all dead. Ordering)
               (equalsInteger eta eta)
               [ (/\dead ->
                    case
                      (all dead. Ordering)
                      (lessThanEqualsInteger eta eta)
                      [(/\dead -> GT), (/\dead -> LT)]
                      {all dead. dead})
               , (/\dead -> EQ) ]
               {all dead. dead})
          (\(x : integer) (y : integer) -> lessThanInteger x y)
          (\(x : integer) (y : integer) -> lessThanEqualsInteger x y)
          (\(x : integer) (y : integer) ->
             ifThenElse {bool} (lessThanEqualsInteger x y) False True)
          (\(x : integer) (y : integer) ->
             ifThenElse {bool} (lessThanInteger x y) False True)
          (\(x : integer) (y : integer) ->
             case
               (all dead. integer)
               (lessThanEqualsInteger x y)
               [(/\dead -> x), (/\dead -> y)]
               {all dead. dead})
          (\(x : integer) (y : integer) ->
             case
               (all dead. integer)
               (lessThanEqualsInteger x y)
               [(/\dead -> y), (/\dead -> x)]
               {all dead. dead})
  in
  letrec
    !go : List (Tuple2 integer ChessSet) -> List ChessSet
      = \(ds : List (Tuple2 integer ChessSet)) ->
          List_match
            {Tuple2 integer ChessSet}
            ds
            {all dead. List ChessSet}
            (/\dead -> Nil {ChessSet})
            (\(x : Tuple2 integer ChessSet)
              (xs : List (Tuple2 integer ChessSet)) ->
               /\dead ->
                 Cons
                   {ChessSet}
                   (Tuple2_match
                      {integer}
                      {ChessSet}
                      x
                      {ChessSet}
                      (\(ds : integer) (b : ChessSet) -> b))
                   (go xs))
            {all dead. dead}
  in
  letrec
    !go : List (Tuple2 integer ChessSet) -> List (Tuple2 integer ChessSet)
      = \(ds : List (Tuple2 integer ChessSet)) ->
          List_match
            {Tuple2 integer ChessSet}
            ds
            {all dead. List (Tuple2 integer ChessSet)}
            (/\dead -> Nil {Tuple2 integer ChessSet})
            (\(x : Tuple2 integer ChessSet)
              (xs : List (Tuple2 integer ChessSet)) ->
               /\dead -> Cons {Tuple2 integer ChessSet} x (go xs))
            {all dead. dead}
  in
  letrec
    !go : List integer -> List ChessSet -> List (Tuple2 integer ChessSet)
      = \(ds : List integer) (_bs : List ChessSet) ->
          List_match
            {integer}
            ds
            {all dead. List (Tuple2 integer ChessSet)}
            (/\dead -> Nil {Tuple2 integer ChessSet})
            (\(ipv : integer) (ipv : List integer) ->
               /\dead ->
                 List_match
                   {ChessSet}
                   _bs
                   {all dead. List (Tuple2 integer ChessSet)}
                   (/\dead -> Nil {Tuple2 integer ChessSet})
                   (\(ipv : ChessSet) (ipv : List ChessSet) ->
                      /\dead ->
                        Cons
                          {Tuple2 integer ChessSet}
                          (Tuple2 {integer} {ChessSet} ipv ipv)
                          (go ipv ipv))
                   {all dead. dead})
            {all dead. dead}
  in
  letrec
    !depthSearch :
       all a.
         (\a -> a -> a -> bool) a ->
         integer ->
         List a ->
         (a -> List a) ->
         (a -> bool) ->
         List a
      = /\a ->
          \(`$dEq` : (\a -> a -> a -> bool) a)
           (depth : integer)
           (q : List a)
           (growFn : a -> List a)
           (finFn : a -> bool) ->
            case
              (all dead. List a)
              (equalsInteger 0 depth)
              [ (/\dead ->
                   case
                     (all dead. List a)
                     (List_match
                        {a}
                        q
                        {bool}
                        True
                        (\(ipv : a) (ipv : List a) -> False))
                     [ (/\dead ->
                          case
                            (all dead. List a)
                            (finFn
                               (List_match
                                  {a}
                                  q
                                  {all dead. a}
                                  (/\dead -> error {a})
                                  (\(h : a) (ds : List a) -> /\dead -> h)
                                  {all dead. dead}))
                            [ (/\dead ->
                                 depthSearch
                                   {a}
                                   `$dEq`
                                   (subtractInteger depth 1)
                                   (let
                                     !list : List a
                                       = growFn
                                           (List_match
                                              {a}
                                              q
                                              {all dead. a}
                                              (/\dead -> error {a})
                                              (\(h : a) (ds : List a) ->
                                                 /\dead -> h)
                                              {all dead. dead})
                                     !q : List a
                                       = List_match
                                           {a}
                                           q
                                           {all dead. List a}
                                           (/\dead -> error {List a})
                                           (\(ds : a) (t : List a) ->
                                              /\dead -> t)
                                           {all dead. dead}
                                   in
                                   letrec
                                     !go : List a -> List a
                                       = \(ds : List a) ->
                                           List_match
                                             {a}
                                             ds
                                             {all dead. List a}
                                             (/\dead -> q)
                                             (\(x : a) (xs : List a) ->
                                                /\dead -> Cons {a} x (go xs))
                                             {all dead. dead}
                                   in
                                   go list)
                                   growFn
                                   finFn)
                            , (/\dead ->
                                 Cons
                                   {a}
                                   (List_match
                                      {a}
                                      q
                                      {all dead. a}
                                      (/\dead -> error {a})
                                      (\(h : a) (ds : List a) -> /\dead -> h)
                                      {all dead. dead})
                                   (depthSearch
                                      {a}
                                      `$dEq`
                                      (subtractInteger depth 1)
                                      (List_match
                                         {a}
                                         q
                                         {all dead. List a}
                                         (/\dead -> error {List a})
                                         (\(ds : a) (t : List a) -> /\dead -> t)
                                         {all dead. dead})
                                      growFn
                                      finFn)) ]
                            {all dead. dead})
                     , (/\dead -> Nil {a}) ]
                     {all dead. dead})
              , (/\dead -> Nil {a}) ]
              {all dead. dead}
  in
  let
    !`$p1Ord` : all a. Ord a -> (\a -> a -> a -> bool) a
      = /\a ->
          \(v : Ord a) ->
            Ord_match
              {a}
              v
              {(\a -> a -> a -> bool) a}
              (\(v : (\a -> a -> a -> bool) a)
                (v : a -> a -> Ordering)
                (v : a -> a -> bool)
                (v : a -> a -> bool)
                (v : a -> a -> bool)
                (v : a -> a -> bool)
                (v : a -> a -> a)
                (v : a -> a -> a) ->
                 v)
    !compare : all a. Ord a -> a -> a -> Ordering
      = /\a ->
          \(v : Ord a) ->
            Ord_match
              {a}
              v
              {a -> a -> Ordering}
              (\(v : (\a -> a -> a -> bool) a)
                (v : a -> a -> Ordering)
                (v : a -> a -> bool)
                (v : a -> a -> bool)
                (v : a -> a -> bool)
                (v : a -> a -> bool)
                (v : a -> a -> a)
                (v : a -> a -> a) ->
                 v)
  in
  letrec
    !quickSort : all a. Ord a -> List a -> List a
      = /\a ->
          \(`$dOrd` : Ord a) (ds : List a) ->
            List_match
              {a}
              ds
              {all dead. List a}
              (/\dead -> Nil {a})
              (\(x : a) (xs : List a) ->
                 /\dead ->
                   let
                     !xs : List a
                       = let
                         !xs : List a
                           = quickSort
                               {a}
                               `$dOrd`
                               ((let
                                    a = List a
                                  in
                                  \(c : a -> a -> a) (n : a) ->
                                    letrec
                                      !go : List a -> a
                                        = \(ds : List a) ->
                                            List_match
                                              {a}
                                              ds
                                              {all dead. a}
                                              (/\dead -> n)
                                              (\(y : a) (ys : List a) ->
                                                 /\dead ->
                                                   let
                                                     !ds : a = go ys
                                                   in
                                                   case
                                                     (all dead. a)
                                                     (Ord_match
                                                        {a}
                                                        `$dOrd`
                                                        {a -> a -> bool}
                                                        (\(v :
                                                             (\a ->
                                                                a -> a -> bool)
                                                               a)
                                                          (v :
                                                             a -> a -> Ordering)
                                                          (v : a -> a -> bool)
                                                          (v : a -> a -> bool)
                                                          (v : a -> a -> bool)
                                                          (v : a -> a -> bool)
                                                          (v : a -> a -> a)
                                                          (v : a -> a -> a) ->
                                                           v)
                                                        y
                                                        x)
                                                     [ (/\dead -> ds)
                                                     , (/\dead -> c y ds) ]
                                                     {all dead. dead})
                                              {all dead. dead}
                                    in
                                    go xs)
                                  (\(ds : a) (ds : List a) -> Cons {a} ds ds)
                                  (Nil {a}))
                       in
                       (let
                           b = List a
                         in
                         \(c : a -> b -> b) (n : b) -> c x n)
                         (\(ds : a) (ds : List a) -> Cons {a} ds ds)
                         xs
                   in
                   (let
                       b = List a
                     in
                     \(c : a -> b -> b) (n : b) ->
                       letrec
                         !go : List a -> b
                           = \(ds : List a) ->
                               List_match
                                 {a}
                                 ds
                                 {all dead. b}
                                 (/\dead -> n)
                                 (\(y : a) (ys : List a) ->
                                    /\dead -> c y (go ys))
                                 {all dead. dead}
                       in
                       let
                         !eta : List a
                           = quickSort
                               {a}
                               `$dOrd`
                               ((let
                                    a = List a
                                  in
                                  \(c : a -> a -> a) (n : a) ->
                                    letrec
                                      !go : List a -> a
                                        = \(ds : List a) ->
                                            List_match
                                              {a}
                                              ds
                                              {all dead. a}
                                              (/\dead -> n)
                                              (\(y : a) (ys : List a) ->
                                                 /\dead ->
                                                   let
                                                     !ds : a = go ys
                                                   in
                                                   case
                                                     (all dead. a)
                                                     (Ord_match
                                                        {a}
                                                        `$dOrd`
                                                        {a -> a -> bool}
                                                        (\(v :
                                                             (\a ->
                                                                a -> a -> bool)
                                                               a)
                                                          (v :
                                                             a -> a -> Ordering)
                                                          (v : a -> a -> bool)
                                                          (v : a -> a -> bool)
                                                          (v : a -> a -> bool)
                                                          (v : a -> a -> bool)
                                                          (v : a -> a -> a)
                                                          (v : a -> a -> a) ->
                                                           v)
                                                        y
                                                        x)
                                                     [ (/\dead -> ds)
                                                     , (/\dead -> c y ds) ]
                                                     {all dead. dead})
                                              {all dead. dead}
                                    in
                                    go xs)
                                  (\(ds : a) (ds : List a) -> Cons {a} ds ds)
                                  (Nil {a}))
                       in
                       go eta)
                     (\(ds : a) (ds : List a) -> Cons {a} ds ds)
                     xs)
              {all dead. dead}
  in
  let
    !interval : integer -> integer -> List integer
      = \(a : integer) (b : integer) ->
          letrec
            !go : integer -> List integer
              = \(a : integer) ->
                  case
                    (all dead. List integer)
                    (ifThenElse {bool} (lessThanEqualsInteger a b) False True)
                    [ (/\dead -> Cons {integer} a (go (addInteger 1 a)))
                    , (/\dead -> Nil {integer}) ]
                    {all dead. dead}
          in
          go a
    !length : all a. List a -> integer
      = /\a ->
          letrec
            !go : List a -> integer
              = \(ds : List a) ->
                  List_match
                    {a}
                    ds
                    {integer}
                    0
                    (\(ds : a) (xs : List a) -> addInteger 1 (go xs))
          in
          \(eta : List a) -> go eta
    data Direction | Direction_match where
      DL : Direction
      DR : Direction
      LD : Direction
      LU : Direction
      RD : Direction
      RU : Direction
      UL : Direction
      UR : Direction
    !move : Direction -> Tuple2 integer integer -> Tuple2 integer integer
      = \(ds : Direction) (ds : Tuple2 integer integer) ->
          Direction_match
            ds
            {all dead. Tuple2 integer integer}
            (/\dead ->
               Tuple2_match
                 {integer}
                 {integer}
                 ds
                 {Tuple2 integer integer}
                 (\(x : integer) (y : integer) ->
                    Tuple2
                      {integer}
                      {integer}
                      (subtractInteger x 1)
                      (addInteger 2 y)))
            (/\dead ->
               Tuple2_match
                 {integer}
                 {integer}
                 ds
                 {Tuple2 integer integer}
                 (\(x : integer) (y : integer) ->
                    Tuple2
                      {integer}
                      {integer}
                      (addInteger 1 x)
                      (addInteger 2 y)))
            (/\dead ->
               Tuple2_match
                 {integer}
                 {integer}
                 ds
                 {Tuple2 integer integer}
                 (\(x : integer) (y : integer) ->
                    Tuple2
                      {integer}
                      {integer}
                      (subtractInteger x 2)
                      (addInteger 1 y)))
            (/\dead ->
               Tuple2_match
                 {integer}
                 {integer}
                 ds
                 {Tuple2 integer integer}
                 (\(x : integer) (y : integer) ->
                    Tuple2
                      {integer}
                      {integer}
                      (subtractInteger x 2)
                      (subtractInteger y 1)))
            (/\dead ->
               Tuple2_match
                 {integer}
                 {integer}
                 ds
                 {Tuple2 integer integer}
                 (\(x : integer) (y : integer) ->
                    Tuple2
                      {integer}
                      {integer}
                      (addInteger 2 x)
                      (addInteger 1 y)))
            (/\dead ->
               Tuple2_match
                 {integer}
                 {integer}
                 ds
                 {Tuple2 integer integer}
                 (\(x : integer) (y : integer) ->
                    Tuple2
                      {integer}
                      {integer}
                      (addInteger 2 x)
                      (subtractInteger y 1)))
            (/\dead ->
               Tuple2_match
                 {integer}
                 {integer}
                 ds
                 {Tuple2 integer integer}
                 (\(x : integer) (y : integer) ->
                    Tuple2
                      {integer}
                      {integer}
                      (subtractInteger x 1)
                      (subtractInteger y 2)))
            (/\dead ->
               Tuple2_match
                 {integer}
                 {integer}
                 ds
                 {Tuple2 integer integer}
                 (\(x : integer) (y : integer) ->
                    Tuple2
                      {integer}
                      {integer}
                      (addInteger 1 x)
                      (subtractInteger y 2)))
            {all dead. dead}
  in
  letrec
    !notIn : all a. (\a -> a -> a -> bool) a -> a -> List a -> bool
      = /\a ->
          \(`$dEq` : (\a -> a -> a -> bool) a) (ds : a) (ds : List a) ->
            List_match
              {a}
              ds
              {bool}
              True
              (\(a : a) (as : List a) ->
                 case
                   (all dead. bool)
                   (case bool (`$dEq` ds a) [True, False])
                   [(/\dead -> False), (/\dead -> notIn {a} `$dEq` ds as)]
                   {all dead. dead})
  in
  let
    !canMoveTo :
       Tuple2 integer integer -> ChessSet -> bool
      = \(t : Tuple2 integer integer)
         (board : ChessSet) ->
          Tuple2_match
            {integer}
            {integer}
            t
            {bool}
            (\(x : integer)
              (y : integer) ->
               ChessSet_match
                 board
                 {bool}
                 (\(ipv : integer)
                   (ipv : integer)
                   (ipv : Maybe (Tuple2 integer integer))
                   (ipv : List (Tuple2 integer integer)) ->
                    case
                      (all dead. bool)
                      (ifThenElse {bool} (lessThanInteger x 1) False True)
                      [ (/\dead -> False)
                      , (/\dead ->
                           case
                             (all dead. bool)
                             (lessThanEqualsInteger x ipv)
                             [ (/\dead -> False)
                             , (/\dead ->
                                  case
                                    (all dead. bool)
                                    (ifThenElse
                                       {bool}
                                       (lessThanInteger y 1)
                                       False
                                       True)
                                    [ (/\dead -> False)
                                    , (/\dead ->
                                         case
                                           (all dead. bool)
                                           (lessThanEqualsInteger y ipv)
                                           [ (/\dead -> False)
                                           , (/\dead ->
                                                notIn
                                                  {Tuple2 integer integer}
                                                  (\(ds :
                                                       Tuple2 integer integer)
                                                    (ds :
                                                       Tuple2
                                                         integer
                                                         integer) ->
                                                     Tuple2_match
                                                       {integer}
                                                       {integer}
                                                       ds
                                                       {bool}
                                                       (\(a : integer)
                                                         (b : integer) ->
                                                          Tuple2_match
                                                            {integer}
                                                            {integer}
                                                            ds
                                                            {bool}
                                                            (\(a' : integer)
                                                              (b' : integer) ->
                                                               case
                                                                 (all dead.
                                                                    bool)
                                                                 (equalsInteger
                                                                    a
                                                                    a')
                                                                 [ (/\dead ->
                                                                      False)
                                                                 , (/\dead ->
                                                                      equalsInteger
                                                                        b
                                                                        b') ]
                                                                 {all dead.
                                                                    dead})))
                                                  t
                                                  ipv) ]
                                           {all dead. dead}) ]
                                    {all dead. dead}) ]
                             {all dead. dead}) ]
                      {all dead. dead}))
    !possibleMoves : ChessSet -> List Direction
      = \(board : ChessSet) ->
          ChessSet_match
            board
            {List Direction}
            (\(ipv : integer)
              (ipv : integer)
              (ipv : Maybe (Tuple2 integer integer))
              (ipv : List (Tuple2 integer integer)) ->
               (let
                   a = List Direction
                 in
                 \(c : Direction -> a -> a) ->
                   let
                     !c : Direction -> a -> a
                       = \(ds : Direction) (ds : a) ->
                           case
                             (all dead. a)
                             (canMoveTo
                                (move
                                   ds
                                   (List_match
                                      {Tuple2 integer integer}
                                      ipv
                                      {all dead. Tuple2 integer integer}
                                      (/\dead -> error {Tuple2 integer integer})
                                      (\(t : Tuple2 integer integer)
                                        (ds : List (Tuple2 integer integer)) ->
                                         /\dead -> t)
                                      {all dead. dead}))
                                board)
                             [(/\dead -> ds), (/\dead -> c ds ds)]
                             {all dead. dead}
                   in
                   \(n : a) ->
                     c UL (c UR (c DL (c DR (c LU (c LD (c RU (c RD n))))))))
                 (\(ds : Direction) (ds : List Direction) ->
                    Cons {Direction} ds ds)
                 (Nil {Direction}))
    !deleteFirst : ChessSet -> ChessSet
      = \(ds : ChessSet) ->
          ChessSet_match
            ds
            {ChessSet}
            (\(s : integer)
              (n : integer)
              (ds : Maybe (Tuple2 integer integer))
              (ts : List (Tuple2 integer integer)) ->
               let
                 !f' : Maybe (Tuple2 integer integer)
                   = (let
                         a = Tuple2 integer integer
                       in
                       letrec
                         !rev : List a -> List a -> Maybe a
                           = \(ds : List a) (a : List a) ->
                               List_match
                                 {a}
                                 ds
                                 {all dead. Maybe a}
                                 (/\dead ->
                                    List_match
                                      {a}
                                      a
                                      {all dead. Maybe a}
                                      (/\dead -> error {Maybe a})
                                      (\(ds : a) (ds : List a) ->
                                         /\dead ->
                                           List_match
                                             {a}
                                             ds
                                             {all dead. Maybe a}
                                             (/\dead -> Nothing {a})
                                             (\(a : a) (ds : List a) ->
                                                /\dead -> Just {a} a)
                                             {all dead. dead})
                                      {all dead. dead})
                                 (\(x : a) (xs : List a) ->
                                    /\dead -> rev xs (Cons {a} x a))
                                 {all dead. dead}
                       in
                       \(l : List a) -> rev l (Nil {a}))
                       ts
               in
               letrec
                 !rev :
                    List (Tuple2 integer integer) ->
                    List (Tuple2 integer integer) ->
                    ChessSet
                   = \(ds : List (Tuple2 integer integer))
                      (a : List (Tuple2 integer integer)) ->
                       List_match
                         {Tuple2 integer integer}
                         ds
                         {all dead. ChessSet}
                         (/\dead ->
                            List_match
                              {Tuple2 integer integer}
                              a
                              {all dead. ChessSet}
                              (/\dead ->
                                 let
                                   !ts' : List (Tuple2 integer integer)
                                     = error {List (Tuple2 integer integer)}
                                 in
                                 Board s (subtractInteger n 1) f' ts')
                              (\(ds : Tuple2 integer integer)
                                (as : List (Tuple2 integer integer)) ->
                                 /\dead ->
                                   let
                                     !ts' : List (Tuple2 integer integer)
                                       = (let
                                             a = Tuple2 integer integer
                                           in
                                           letrec
                                             !rev : List a -> List a -> List a
                                               = \(ds : List a) (a : List a) ->
                                                   List_match
                                                     {a}
                                                     ds
                                                     {all dead. List a}
                                                     (/\dead -> a)
                                                     (\(x : a) (xs : List a) ->
                                                        /\dead ->
                                                          rev xs (Cons {a} x a))
                                                     {all dead. dead}
                                           in
                                           \(l : List a) -> rev l (Nil {a}))
                                           as
                                   in
                                   Board s (subtractInteger n 1) f' ts')
                              {all dead. dead})
                         (\(x : Tuple2 integer integer)
                           (xs : List (Tuple2 integer integer)) ->
                            /\dead ->
                              rev xs (Cons {Tuple2 integer integer} x a))
                         {all dead. dead}
               in
               rev ts (Nil {Tuple2 integer integer}))
    !descAndNo : ChessSet -> List (Tuple2 integer ChessSet)
      = \(board : ChessSet) ->
          letrec
            !go : List Direction -> List ChessSet
              = \(ds : List Direction) ->
                  List_match
                    {Direction}
                    ds
                    {all dead. List ChessSet}
                    (/\dead -> Nil {ChessSet})
                    (\(x : Direction) (xs : List Direction) ->
                       /\dead ->
                         Cons
                           {ChessSet}
                           (ChessSet_match
                              board
                              {ChessSet}
                              (\(ipv : integer)
                                (ipv : integer)
                                (ipv : Maybe (Tuple2 integer integer))
                                (ipv : List (Tuple2 integer integer)) ->
                                 let
                                   !t : Tuple2 integer integer
                                     = move
                                         x
                                         (List_match
                                            {Tuple2 integer integer}
                                            ipv
                                            {all dead. Tuple2 integer integer}
                                            (/\dead ->
                                               error {Tuple2 integer integer})
                                            (\(t : Tuple2 integer integer)
                                              (ds :
                                                 List
                                                   (Tuple2 integer integer)) ->
                                               /\dead -> t)
                                            {all dead. dead})
                                 in
                                 Board
                                   ipv
                                   (addInteger 1 ipv)
                                   ipv
                                   (Cons {Tuple2 integer integer} t ipv)))
                           (go xs))
                    {all dead. dead}
          in
          (let
              a = Tuple2 integer ChessSet
            in
            \(g : all b. (a -> b -> b) -> b -> b) ->
              g {List a} (\(ds : a) (ds : List a) -> Cons {a} ds ds) (Nil {a}))
            (/\a ->
               \(c : Tuple2 integer ChessSet -> a -> a) (n : a) ->
                 letrec
                   !go : List ChessSet -> a
                     = \(ds : List ChessSet) ->
                         List_match
                           {ChessSet}
                           ds
                           {all dead. a}
                           (/\dead -> n)
                           (\(y : ChessSet) (ys : List ChessSet) ->
                              /\dead ->
                                let
                                  !ds : a = go ys
                                in
                                c
                                  (Tuple2
                                     {integer}
                                     {ChessSet}
                                     (length
                                        {Direction}
                                        (possibleMoves (deleteFirst y)))
                                     y)
                                  ds)
                           {all dead. dead}
                 in
                 let
                   !eta : List ChessSet = go (possibleMoves board)
                 in
                 go eta)
  in
  \(depth : integer)
   (boardSize : integer) ->
    depthSearch
      {Tuple2 integer ChessSet}
      (\(ds : Tuple2 integer ChessSet) (ds : Tuple2 integer ChessSet) ->
         Tuple2_match
           {integer}
           {ChessSet}
           ds
           {bool}
           (\(a : integer) (b : ChessSet) ->
              Tuple2_match
                {integer}
                {ChessSet}
                ds
                {bool}
                (\(a' : integer) (b' : ChessSet) ->
                   case
                     (all dead. bool)
                     (equalsInteger a a')
                     [(/\dead -> False), (/\dead -> True)]
                     {all dead. dead})))
      depth
      (let
        !list :
           List (Tuple2 integer ChessSet)
          = let
            !l :
               List ChessSet
              = (let
                    a = List ChessSet
                  in
                  \(c : ChessSet -> a -> a)
                   (n : a) ->
                    letrec
                      !go :
                         List integer -> a
                        = \(ds : List integer) ->
                            List_match
                              {integer}
                              ds
                              {all dead. a}
                              (/\dead -> n)
                              (\(y : integer)
                                (ys : List integer) ->
                                 /\dead ->
                                   let
                                     !ds : a = go ys
                                   in
                                   letrec
                                     !go :
                                        List integer -> a
                                       = \(ds : List integer) ->
                                           List_match
                                             {integer}
                                             ds
                                             {all dead. a}
                                             (/\dead -> ds)
                                             (\(y : integer) ->
                                                let
                                                  !st : Tuple2 integer integer
                                                    = Tuple2
                                                        {integer}
                                                        {integer}
                                                        y
                                                        y
                                                in
                                                \(ys : List integer) ->
                                                  /\dead ->
                                                    let
                                                      !ds : a = go ys
                                                    in
                                                    c
                                                      (case
                                                         (all dead. ChessSet)
                                                         (equalsInteger
                                                            0
                                                            (remainderInteger
                                                               boardSize
                                                               2))
                                                         [ (/\dead ->
                                                              error {ChessSet})
                                                         , (/\dead ->
                                                              Board
                                                                boardSize
                                                                1
                                                                (Just
                                                                   {Tuple2
                                                                      integer
                                                                      integer}
                                                                   st)
                                                                ((let
                                                                     a
                                                                       = Tuple2
                                                                           integer
                                                                           integer
                                                                   in
                                                                   \(g :
                                                                       all b.
                                                                         (a ->
                                                                          b ->
                                                                          b) ->
                                                                         b ->
                                                                         b) ->
                                                                     g
                                                                       {List a}
                                                                       (\(ds :
                                                                            a)
                                                                         (ds :
                                                                            List
                                                                              a) ->
                                                                          Cons
                                                                            {a}
                                                                            ds
                                                                            ds)
                                                                       (Nil
                                                                          {a}))
                                                                   (/\a ->
                                                                      \(c :
                                                                          Tuple2
                                                                            integer
                                                                            integer ->
                                                                          a ->
                                                                          a)
                                                                       (n :
                                                                          a) ->
                                                                        c
                                                                          st
                                                                          n))) ]
                                                         {all dead. dead})
                                                      ds)
                                             {all dead. dead}
                                   in
                                   let
                                     !eta : List integer = interval 1 boardSize
                                   in
                                   go eta)
                              {all dead. dead}
                    in
                    let
                      !eta : List integer = interval 1 boardSize
                    in
                    go eta)
                  (\(ds : ChessSet) (ds : List ChessSet) ->
                     Cons {ChessSet} ds ds)
                  (Nil {ChessSet})
            !numStarts : integer = length {ChessSet} l
            !eta : List integer
              = let
                !x : integer = subtractInteger 1 numStarts
              in
              letrec
                !go : integer -> List integer
                  = \(n : integer) ->
                      case
                        (all dead. List integer)
                        (lessThanEqualsInteger n 0)
                        [ (/\dead ->
                             Cons {integer} x (go (subtractInteger n 1)))
                        , (/\dead -> Nil {integer}) ]
                        {all dead. dead}
              in
              go numStarts
          in
          go eta l
      in
      go list)
      (\(ds : Tuple2 integer ChessSet) ->
         Tuple2_match
           {integer}
           {ChessSet}
           ds
           {List (Tuple2 integer ChessSet)}
           (\(x : integer) (y : ChessSet) ->
              (let
                  !a : integer = addInteger 1 x
                in
                letrec
                  !go : List ChessSet -> List (Tuple2 integer ChessSet)
                    = \(ds : List ChessSet) ->
                        List_match
                          {ChessSet}
                          ds
                          {all dead. List (Tuple2 integer ChessSet)}
                          (/\dead -> Nil {Tuple2 integer ChessSet})
                          (\(x : ChessSet) (xs : List ChessSet) ->
                             /\dead ->
                               Cons
                                 {Tuple2 integer ChessSet}
                                 (Tuple2 {integer} {ChessSet} a x)
                                 (go xs))
                          {all dead. dead}
                in
                \(eta : List ChessSet) -> go eta)
                (ChessSet_match
                   y
                   {List ChessSet}
                   (\(ipv : integer)
                     (ipv : integer)
                     (ipv : Maybe (Tuple2 integer integer))
                     (ipv : List (Tuple2 integer integer)) ->
                      let
                        !`$j` :
                           integer -> integer -> Tuple2 integer integer -> bool
                          = \(ipv : integer)
                             (ipv : integer)
                             (t : Tuple2 integer integer) ->
                              let
                                !conrep : integer = addInteger 1 ipv
                              in
                              equalsInteger
                                0
                                (length
                                   {Direction}
                                   (possibleMoves
                                      (Board
                                         ipv
                                         conrep
                                         ipv
                                         (Cons
                                            {Tuple2 integer integer}
                                            t
                                            ipv))))
                        !singles : List ChessSet
                          = (let
                                a = List ChessSet
                              in
                              \(c : ChessSet -> a -> a) (n : a) ->
                                (let
                                    a = Tuple2 integer ChessSet
                                  in
                                  /\b ->
                                    \(k : a -> b -> b) (z : b) ->
                                      letrec
                                        !go : List a -> b
                                          = \(ds : List a) ->
                                              List_match
                                                {a}
                                                ds
                                                {all dead. b}
                                                (/\dead -> z)
                                                (\(y : a) (ys : List a) ->
                                                   /\dead -> k y (go ys))
                                                {all dead. dead}
                                      in
                                      \(eta : List a) -> go eta)
                                  {a}
                                  (\(ds : Tuple2 integer ChessSet) (ds : a) ->
                                     Tuple2_match
                                       {integer}
                                       {ChessSet}
                                       ds
                                       {a}
                                       (\(y : integer) (x : ChessSet) ->
                                          case
                                            (all dead. a)
                                            (equalsInteger 1 y)
                                            [(/\dead -> ds), (/\dead -> c x ds)]
                                            {all dead. dead}))
                                  n
                                  (descAndNo y))
                              (\(ds : ChessSet) (ds : List ChessSet) ->
                                 Cons {ChessSet} ds ds)
                              (Nil {ChessSet})
                      in
                      case
                        (all dead. List ChessSet)
                        (case
                           (all dead. bool)
                           (canMoveTo
                              (Maybe_match
                                 {Tuple2 integer integer}
                                 ipv
                                 {all dead. Tuple2 integer integer}
                                 (\(tile : Tuple2 integer integer) ->
                                    /\dead -> tile)
                                 (/\dead -> error {Tuple2 integer integer})
                                 {all dead. dead})
                              (deleteFirst y))
                           [ (/\dead -> False)
                           , (/\dead ->
                                Maybe_match
                                  {Tuple2 integer integer}
                                  ipv
                                  {all dead. bool}
                                  (\(tile : Tuple2 integer integer) ->
                                     /\dead ->
                                       Tuple2_match
                                         {integer}
                                         {integer}
                                         tile
                                         {bool}
                                         (\(ipv : integer) (ipv : integer) ->
                                            `$j` ipv ipv tile))
                                  (/\dead ->
                                     Tuple2_match
                                       {integer}
                                       {integer}
                                       (error {Tuple2 integer integer})
                                       {bool}
                                       (\(ipv : integer) (ipv : integer) ->
                                          `$j`
                                            ipv
                                            ipv
                                            (error {Tuple2 integer integer})))
                                  {all dead. dead}) ]
                           {all dead. dead})
                        [ (/\dead ->
                             let
                               !l : integer = length {ChessSet} singles
                             in
                             case
                               (all dead. List ChessSet)
                               (equalsInteger 0 l)
                               [ (/\dead ->
                                    case
                                      (all dead. List ChessSet)
                                      (equalsInteger 1 l)
                                      [ (/\dead -> Nil {ChessSet})
                                      , (/\dead -> singles) ]
                                      {all dead. dead})
                               , (/\dead ->
                                    go
                                      (quickSort
                                         {Tuple2 integer ChessSet}
                                         (CConsOrd
                                            {Tuple2 integer ChessSet}
                                            (\(eta : Tuple2 integer ChessSet)
                                              (eta : Tuple2 integer ChessSet) ->
                                               Tuple2_match
                                                 {integer}
                                                 {ChessSet}
                                                 eta
                                                 {bool}
                                                 (\(a : integer)
                                                   (b : ChessSet) ->
                                                    Tuple2_match
                                                      {integer}
                                                      {ChessSet}
                                                      eta
                                                      {bool}
                                                      (\(a' : integer)
                                                        (b' : ChessSet) ->
                                                         case
                                                           (all dead. bool)
                                                           (`$p1Ord`
                                                              {integer}
                                                              v
                                                              a
                                                              a')
                                                           [ (/\dead -> False)
                                                           , (/\dead ->
                                                                `$p1Ord`
                                                                  {ChessSet}
                                                                  v
                                                                  b
                                                                  b') ]
                                                           {all dead. dead})))
                                            (\(ds : Tuple2 integer ChessSet)
                                              (ds : Tuple2 integer ChessSet) ->
                                               Tuple2_match
                                                 {integer}
                                                 {ChessSet}
                                                 ds
                                                 {Ordering}
                                                 (\(a : integer)
                                                   (b : ChessSet) ->
                                                    Tuple2_match
                                                      {integer}
                                                      {ChessSet}
                                                      ds
                                                      {Ordering}
                                                      (\(a' : integer) ->
                                                         let
                                                           ~defaultBody :
                                                              Ordering
                                                             = compare
                                                                 {integer}
                                                                 v
                                                                 a
                                                                 a'
                                                         in
                                                         \(b' : ChessSet) ->
                                                           Ordering_match
                                                             (compare
                                                                {integer}
                                                                v
                                                                a
                                                                a')
                                                             {all dead.
                                                                Ordering}
                                                             (/\dead ->
                                                                compare
                                                                  {ChessSet}
                                                                  v
                                                                  b
                                                                  b')
                                                             (/\dead ->
                                                                defaultBody)
                                                             (/\dead ->
                                                                defaultBody)
                                                             {all dead. dead})))
                                            (\(x : Tuple2 integer ChessSet)
                                              (y : Tuple2 integer ChessSet) ->
                                               Tuple2_match
                                                 {integer}
                                                 {ChessSet}
                                                 x
                                                 {bool}
                                                 (\(ipv : integer)
                                                   (ipv : ChessSet) ->
                                                    Tuple2_match
                                                      {integer}
                                                      {ChessSet}
                                                      y
                                                      {bool}
                                                      (\(ipv : integer)
                                                        (ipv : ChessSet) ->
                                                         Ordering_match
                                                           (compare
                                                              {integer}
                                                              v
                                                              ipv
                                                              ipv)
                                                           {all dead. bool}
                                                           (/\dead ->
                                                              Ordering_match
                                                                (compare
                                                                   {ChessSet}
                                                                   v
                                                                   ipv
                                                                   ipv)
                                                                {all dead. bool}
                                                                (/\dead ->
                                                                   False)
                                                                (/\dead ->
                                                                   False)
                                                                (/\dead -> True)
                                                                {all dead.
                                                                   dead})
                                                           (/\dead -> False)
                                                           (/\dead -> True)
                                                           {all dead. dead})))
                                            (\(x : Tuple2 integer ChessSet)
                                              (y : Tuple2 integer ChessSet) ->
                                               Tuple2_match
                                                 {integer}
                                                 {ChessSet}
                                                 x
                                                 {bool}
                                                 (\(ipv : integer)
                                                   (ipv : ChessSet) ->
                                                    Tuple2_match
                                                      {integer}
                                                      {ChessSet}
                                                      y
                                                      {bool}
                                                      (\(ipv : integer)
                                                        (ipv : ChessSet) ->
                                                         Ordering_match
                                                           (compare
                                                              {integer}
                                                              v
                                                              ipv
                                                              ipv)
                                                           {all dead. bool}
                                                           (/\dead ->
                                                              Ordering_match
                                                                (compare
                                                                   {ChessSet}
                                                                   v
                                                                   ipv
                                                                   ipv)
                                                                {all dead. bool}
                                                                (/\dead -> True)
                                                                (/\dead ->
                                                                   False)
                                                                (/\dead -> True)
                                                                {all dead.
                                                                   dead})
                                                           (/\dead -> False)
                                                           (/\dead -> True)
                                                           {all dead. dead})))
                                            (\(x : Tuple2 integer ChessSet)
                                              (y : Tuple2 integer ChessSet) ->
                                               Tuple2_match
                                                 {integer}
                                                 {ChessSet}
                                                 x
                                                 {bool}
                                                 (\(ipv : integer)
                                                   (ipv : ChessSet) ->
                                                    Tuple2_match
                                                      {integer}
                                                      {ChessSet}
                                                      y
                                                      {bool}
                                                      (\(ipv : integer)
                                                        (ipv : ChessSet) ->
                                                         Ordering_match
                                                           (compare
                                                              {integer}
                                                              v
                                                              ipv
                                                              ipv)
                                                           {all dead. bool}
                                                           (/\dead ->
                                                              Ordering_match
                                                                (compare
                                                                   {ChessSet}
                                                                   v
                                                                   ipv
                                                                   ipv)
                                                                {all dead. bool}
                                                                (/\dead ->
                                                                   False)
                                                                (/\dead -> True)
                                                                (/\dead ->
                                                                   False)
                                                                {all dead.
                                                                   dead})
                                                           (/\dead -> True)
                                                           (/\dead -> False)
                                                           {all dead. dead})))
                                            (\(x : Tuple2 integer ChessSet)
                                              (y : Tuple2 integer ChessSet) ->
                                               Tuple2_match
                                                 {integer}
                                                 {ChessSet}
                                                 x
                                                 {bool}
                                                 (\(ipv : integer)
                                                   (ipv : ChessSet) ->
                                                    Tuple2_match
                                                      {integer}
                                                      {ChessSet}
                                                      y
                                                      {bool}
                                                      (\(ipv : integer)
                                                        (ipv : ChessSet) ->
                                                         Ordering_match
                                                           (compare
                                                              {integer}
                                                              v
                                                              ipv
                                                              ipv)
                                                           {all dead. bool}
                                                           (/\dead ->
                                                              Ordering_match
                                                                (compare
                                                                   {ChessSet}
                                                                   v
                                                                   ipv
                                                                   ipv)
                                                                {all dead. bool}
                                                                (/\dead -> True)
                                                                (/\dead -> True)
                                                                (/\dead ->
                                                                   False)
                                                                {all dead.
                                                                   dead})
                                                           (/\dead -> True)
                                                           (/\dead -> False)
                                                           {all dead. dead})))
                                            (\(x : Tuple2 integer ChessSet)
                                              (y : Tuple2 integer ChessSet) ->
                                               Tuple2_match
                                                 {integer}
                                                 {ChessSet}
                                                 x
                                                 {Tuple2 integer ChessSet}
                                                 (\(ipv : integer)
                                                   (ipv : ChessSet) ->
                                                    Tuple2_match
                                                      {integer}
                                                      {ChessSet}
                                                      y
                                                      {Tuple2 integer ChessSet}
                                                      (\(ipv : integer)
                                                        (ipv : ChessSet) ->
                                                         Ordering_match
                                                           (compare
                                                              {integer}
                                                              v
                                                              ipv
                                                              ipv)
                                                           {all dead.
                                                              Tuple2
                                                                integer
                                                                ChessSet}
                                                           (/\dead ->
                                                              Ordering_match
                                                                (compare
                                                                   {ChessSet}
                                                                   v
                                                                   ipv
                                                                   ipv)
                                                                {all dead.
                                                                   Tuple2
                                                                     integer
                                                                     ChessSet}
                                                                (/\dead -> y)
                                                                (/\dead -> x)
                                                                (/\dead -> y)
                                                                {all dead.
                                                                   dead})
                                                           (/\dead -> x)
                                                           (/\dead -> y)
                                                           {all dead. dead})))
                                            (\(x : Tuple2 integer ChessSet)
                                              (y : Tuple2 integer ChessSet) ->
                                               Tuple2_match
                                                 {integer}
                                                 {ChessSet}
                                                 x
                                                 {Tuple2 integer ChessSet}
                                                 (\(ipv : integer)
                                                   (ipv : ChessSet) ->
                                                    Tuple2_match
                                                      {integer}
                                                      {ChessSet}
                                                      y
                                                      {Tuple2 integer ChessSet}
                                                      (\(ipv : integer)
                                                        (ipv : ChessSet) ->
                                                         Ordering_match
                                                           (compare
                                                              {integer}
                                                              v
                                                              ipv
                                                              ipv)
                                                           {all dead.
                                                              Tuple2
                                                                integer
                                                                ChessSet}
                                                           (/\dead ->
                                                              Ordering_match
                                                                (compare
                                                                   {ChessSet}
                                                                   v
                                                                   ipv
                                                                   ipv)
                                                                {all dead.
                                                                   Tuple2
                                                                     integer
                                                                     ChessSet}
                                                                (/\dead -> x)
                                                                (/\dead -> y)
                                                                (/\dead -> x)
                                                                {all dead.
                                                                   dead})
                                                           (/\dead -> y)
                                                           (/\dead -> x)
                                                           {all dead. dead}))))
                                         (descAndNo y))) ]
                               {all dead. dead})
                        , (/\dead -> Nil {ChessSet}) ]
                        {all dead. dead}))))
      (\(ds : Tuple2 integer ChessSet) ->
         Tuple2_match
           {integer}
           {ChessSet}
           ds
           {bool}
           (\(ds : integer) (y : ChessSet) ->
              ChessSet_match
                y
                {bool}
                (\(ipv : integer)
                  (ipv : integer)
                  (ipv : Maybe (Tuple2 integer integer))
                  (ipv : List (Tuple2 integer integer)) ->
                   case
                     (all dead. bool)
                     (equalsInteger ipv (multiplyInteger ipv ipv))
                     [ (/\dead -> False)
                     , (/\dead ->
                          canMoveTo
                            (Maybe_match
                               {Tuple2 integer integer}
                               ipv
                               {all dead. Tuple2 integer integer}
                               (\(tile : Tuple2 integer integer) ->
                                  /\dead -> tile)
                               (/\dead -> error {Tuple2 integer integer})
                               {all dead. dead})
                            (deleteFirst y)) ]
                     {all dead. dead}))))
  10
  4