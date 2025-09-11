(let
    data (Tuple2 :: * -> * -> *) a b | Tuple2_match where
      Tuple2 : a -> b -> Tuple2 a b
  in
  letrec
    data (List :: * -> *) a | List_match where
      Nil : List a
      Cons : a -> List a -> List a
  in
  let
    data ConflictSet | ConflictSet_match where
      Known : List integer -> ConflictSet
      Unknown : ConflictSet
    data Assign | Assign_match where
      `Cons=` : integer -> integer -> Assign
  in
  letrec
    !go : List (Tuple2 (List Assign) ConflictSet) -> List (List Assign)
      = \(ds : List (Tuple2 (List Assign) ConflictSet)) ->
          List_match
            {Tuple2 (List Assign) ConflictSet}
            ds
            {all dead. List (List Assign)}
            (/\dead -> Nil {List Assign})
            (\(x : Tuple2 (List Assign) ConflictSet)
              (xs : List (Tuple2 (List Assign) ConflictSet)) ->
               /\dead ->
                 Cons
                   {List Assign}
                   (Tuple2_match
                      {List Assign}
                      {ConflictSet}
                      x
                      {List Assign}
                      (\(a : List Assign) (ds : ConflictSet) -> a))
                   (go xs))
            {all dead. dead}
  in
  letrec
    !go : List ConflictSet -> bool
      = \(ds : List ConflictSet) ->
          List_match
            {ConflictSet}
            ds
            {bool}
            True
            (\(x : ConflictSet) (xs : List ConflictSet) ->
               case
                 (all dead. bool)
                 (ConflictSet_match
                    x
                    {bool}
                    (\(ds : List integer) ->
                       List_match
                         {integer}
                         ds
                         {bool}
                         False
                         (\(a : integer) (as : List integer) -> True))
                    False)
                 [(/\dead -> False), (/\dead -> go xs)]
                 {all dead. dead})
  in
  letrec
    data (Tree :: * -> *) a | Tree_match where
      Node : a -> List (Tree a) -> Tree a
  in
  letrec
    !go :
       List (Tree (Tuple2 (List Assign) ConflictSet)) ->
       List (Tuple2 (List Assign) ConflictSet)
      = \(ds : List (Tree (Tuple2 (List Assign) ConflictSet))) ->
          List_match
            {Tree (Tuple2 (List Assign) ConflictSet)}
            ds
            {all dead. List (Tuple2 (List Assign) ConflictSet)}
            (/\dead -> Nil {Tuple2 (List Assign) ConflictSet})
            (\(x : Tree (Tuple2 (List Assign) ConflictSet))
              (xs : List (Tree (Tuple2 (List Assign) ConflictSet))) ->
               /\dead ->
                 Cons
                   {Tuple2 (List Assign) ConflictSet}
                   (Tree_match
                      {Tuple2 (List Assign) ConflictSet}
                      x
                      {Tuple2 (List Assign) ConflictSet}
                      (\(lab : Tuple2 (List Assign) ConflictSet)
                        (ds : List (Tree (Tuple2 (List Assign) ConflictSet))) ->
                         lab))
                   (go xs))
            {all dead. dead}
  in
  letrec
    !go :
       List (Tree (Tuple2 (List Assign) ConflictSet)) ->
       List (Tuple2 (List Assign) ConflictSet)
      = \(ds : List (Tree (Tuple2 (List Assign) ConflictSet))) ->
          List_match
            {Tree (Tuple2 (List Assign) ConflictSet)}
            ds
            {all dead. List (Tuple2 (List Assign) ConflictSet)}
            (/\dead -> Nil {Tuple2 (List Assign) ConflictSet})
            (\(x : Tree (Tuple2 (List Assign) ConflictSet))
              (xs : List (Tree (Tuple2 (List Assign) ConflictSet))) ->
               /\dead ->
                 Cons
                   {Tuple2 (List Assign) ConflictSet}
                   (Tree_match
                      {Tuple2 (List Assign) ConflictSet}
                      x
                      {Tuple2 (List Assign) ConflictSet}
                      (\(lab : Tuple2 (List Assign) ConflictSet)
                        (ds : List (Tree (Tuple2 (List Assign) ConflictSet))) ->
                         lab))
                   (go xs))
            {all dead. dead}
  in
  let
    data Algorithm | Algorithm_match where
      Bjbt : Algorithm
      Bjbt : Algorithm
      Bm : Algorithm
      Bt : Algorithm
      Fc : Algorithm
    !equalsInteger : integer -> integer -> bool
      = \(x : integer) (y : integer) -> equalsInteger x y
    data Unit | Unit_match where
      Unit : Unit
  in
  letrec
    !deleteBy : all a. (a -> a -> bool) -> a -> List a -> List a
      = /\a ->
          \(ds : a -> a -> bool) (ds : a) (ds : List a) ->
            List_match
              {a}
              ds
              {all dead. List a}
              (/\dead -> Nil {a})
              (\(y : a) (ys : List a) ->
                 /\dead ->
                   case
                     (all dead. List a)
                     (ds ds y)
                     [ (/\dead -> Cons {a} y (deleteBy {a} ds ds ys))
                     , (/\dead -> ys) ]
                     {all dead. dead})
              {all dead. dead}
  in
  let
    !unionBy : all a. (a -> a -> bool) -> List a -> List a -> List a
      = /\a ->
          \(eq : a -> a -> bool) ->
            letrec
              !nubBy' : List a -> List a -> List a
                = \(ds : List a) (ds : List a) ->
                    List_match
                      {a}
                      ds
                      {all dead. List a}
                      (/\dead -> Nil {a})
                      (\(y : a) ->
                         letrec
                           !go : List a -> bool
                             = \(ds : List a) ->
                                 List_match
                                   {a}
                                   ds
                                   {bool}
                                   False
                                   (\(x : a) (xs : List a) ->
                                      case
                                        (all dead. bool)
                                        (eq x y)
                                        [(/\dead -> go xs), (/\dead -> True)]
                                        {all dead. dead})
                         in
                         \(ys : List a) ->
                           /\dead ->
                             case
                               (all dead. List a)
                               (go ds)
                               [ (/\dead ->
                                    Cons {a} y (nubBy' ys (Cons {a} y ds)))
                               , (/\dead -> nubBy' ys ds) ]
                               {all dead. dead})
                      {all dead. dead}
            in
            letrec
              !go : List a -> List a -> List a
                = \(acc : List a) (ds : List a) ->
                    List_match
                      {a}
                      ds
                      {all dead. List a}
                      (/\dead -> acc)
                      (\(x : a) (xs : List a) ->
                         /\dead -> go (deleteBy {a} eq x acc) xs)
                      {all dead. dead}
            in
            \(xs : List a) (ys : List a) ->
              let
                !r : List a = go (nubBy' ys (Nil {a})) xs
              in
              letrec
                !go : List a -> List a
                  = \(ds : List a) ->
                      List_match
                        {a}
                        ds
                        {all dead. List a}
                        (/\dead -> r)
                        (\(x : a) (xs : List a) -> /\dead -> Cons {a} x (go xs))
                        {all dead. dead}
              in
              go xs
  in
  letrec
    !combine :
       List (Tuple2 (List Assign) ConflictSet) -> List integer -> List integer
      = \(ds : List (Tuple2 (List Assign) ConflictSet)) (acc : List integer) ->
          List_match
            {Tuple2 (List Assign) ConflictSet}
            ds
            {all dead. List integer}
            (/\dead -> acc)
            (\(ds : Tuple2 (List Assign) ConflictSet)
              (css : List (Tuple2 (List Assign) ConflictSet)) ->
               /\dead ->
                 Tuple2_match
                   {List Assign}
                   {ConflictSet}
                   ds
                   {List integer}
                   (\(s : List Assign) (ds : ConflictSet) ->
                      ConflictSet_match
                        ds
                        {all dead. List integer}
                        (\(cs : List integer) ->
                           /\dead ->
                             case
                               (all dead. List integer)
                               ((let
                                    !a : integer
                                      = List_match
                                          {Assign}
                                          s
                                          {integer}
                                          0
                                          (\(ds : Assign) (ds : List Assign) ->
                                             Assign_match
                                               ds
                                               {integer}
                                               (\(var : integer)
                                                 (val : integer) ->
                                                  var))
                                  in
                                  letrec
                                    !go : List integer -> bool
                                      = \(ds : List integer) ->
                                          List_match
                                            {integer}
                                            ds
                                            {bool}
                                            True
                                            (\(x : integer)
                                              (xs : List integer) ->
                                               case
                                                 (all dead. bool)
                                                 (equalsInteger a x)
                                                 [ (/\dead -> go xs)
                                                 , (/\dead -> False) ]
                                                 {all dead. dead})
                                  in
                                  \(x : List integer) -> go x)
                                  cs)
                               [ (/\dead ->
                                    combine
                                      css
                                      (unionBy {integer} equalsInteger cs acc))
                               , (/\dead -> cs) ]
                               {all dead. dead})
                        (/\dead ->
                           let
                             !defaultBody : List integer = error {List integer}
                           in
                           Unit_match (error {Unit}) {List integer} defaultBody)
                        {all dead. dead}))
            {all dead. dead}
  in
  letrec
    !rev : List Assign -> List Assign -> List Assign
      = \(ds : List Assign) (a : List Assign) ->
          List_match
            {Assign}
            ds
            {all dead. List Assign}
            (/\dead -> a)
            (\(x : Assign) (xs : List Assign) ->
               /\dead -> rev xs (Cons {Assign} x a))
            {all dead. dead}
  in
  let
    data (Maybe :: * -> *) a | Maybe_match where
      Just : a -> Maybe a
      Nothing : Maybe a
  in
  letrec
    !mapTree : all a b. (a -> b) -> Tree a -> Tree b
      = /\a b ->
          \(f : a -> b) (ds : Tree a) ->
            Tree_match
              {a}
              ds
              {Tree b}
              (\(a : a) (cs : List (Tree a)) ->
                 Node
                   {b}
                   (f a)
                   (let
                     !f : Tree a -> Tree b = mapTree {a} {b} f
                   in
                   letrec
                     !go : List (Tree a) -> List (Tree b)
                       = \(ds : List (Tree a)) ->
                           List_match
                             {Tree a}
                             ds
                             {all dead. List (Tree b)}
                             (/\dead -> Nil {Tree b})
                             (\(x : Tree a) (xs : List (Tree a)) ->
                                /\dead -> Cons {Tree b} (f x) (go xs))
                             {all dead. dead}
                   in
                   go cs))
  in
  let
    !filter : all a. (a -> bool) -> List a -> List a
      = /\a ->
          \(p : a -> bool) ->
            letrec
              !go : List a -> List a
                = \(ds : List a) ->
                    List_match
                      {a}
                      ds
                      {all dead. List a}
                      (/\dead -> Nil {a})
                      (\(x : a) (xs : List a) ->
                         /\dead ->
                           let
                             !xs : List a = go xs
                           in
                           case
                             (all dead. List a)
                             (p x)
                             [(/\dead -> xs), (/\dead -> Cons {a} x xs)]
                             {all dead. dead})
                      {all dead. dead}
            in
            \(eta : List a) -> go eta
    data CSP | CSP_match where
      CSP : integer -> integer -> (Assign -> Assign -> bool) -> CSP
    !bt : CSP -> Tree (List Assign) -> Tree (Tuple2 (List Assign) ConflictSet)
      = \(csp : CSP) ->
          CSP_match
            csp
            {Tree (List Assign) -> Tree (Tuple2 (List Assign) ConflictSet)}
            (\(ipv : integer)
              (ipv : integer)
              (ipv : Assign -> Assign -> bool) ->
               mapTree
                 {List Assign}
                 {Tuple2 (List Assign) ConflictSet}
                 (\(s : List Assign) ->
                    Tuple2
                      {List Assign}
                      {ConflictSet}
                      s
                      (Maybe_match
                         {Tuple2 integer integer}
                         (CSP_match
                            csp
                            {Maybe (Tuple2 integer integer)}
                            (\(ds : integer)
                              (ds : integer)
                              (ds : Assign -> Assign -> bool) ->
                               List_match
                                 {Assign}
                                 s
                                 {all dead. Maybe (Tuple2 integer integer)}
                                 (/\dead -> Nothing {Tuple2 integer integer})
                                 (\(a : Assign) (as : List Assign) ->
                                    /\dead ->
                                      List_match
                                        {Assign}
                                        (filter
                                           {Assign}
                                           (\(eta : Assign) ->
                                              case
                                                bool
                                                (ds a eta)
                                                [True, False])
                                           (rev as (Nil {Assign})))
                                        {all dead.
                                           Maybe (Tuple2 integer integer)}
                                        (/\dead ->
                                           Nothing {Tuple2 integer integer})
                                        (\(b : Assign) (ds : List Assign) ->
                                           /\dead ->
                                             Just
                                               {Tuple2 integer integer}
                                               (Tuple2
                                                  {integer}
                                                  {integer}
                                                  (Assign_match
                                                     a
                                                     {integer}
                                                     (\(var : integer)
                                                       (val : integer) ->
                                                        var))
                                                  (Assign_match
                                                     b
                                                     {integer}
                                                     (\(var : integer)
                                                       (val : integer) ->
                                                        var))))
                                        {all dead. dead})
                                 {all dead. dead}))
                         {all dead. ConflictSet}
                         (\(ds : Tuple2 integer integer) ->
                            /\dead ->
                              Tuple2_match
                                {integer}
                                {integer}
                                ds
                                {ConflictSet}
                                (\(a : integer) (b : integer) ->
                                   Known
                                     ((let
                                          a = List integer
                                        in
                                        \(c : integer -> a -> a) (n : a) ->
                                          c a (c b n))
                                        (\(ds : integer) (ds : List integer) ->
                                           Cons {integer} ds ds)
                                        (Nil {integer}))))
                         (/\dead ->
                            case
                              (all dead. ConflictSet)
                              (equalsInteger
                                 (List_match
                                    {Assign}
                                    s
                                    {integer}
                                    0
                                    (\(ds : Assign) (ds : List Assign) ->
                                       Assign_match
                                         ds
                                         {integer}
                                         (\(var : integer) (val : integer) ->
                                            var)))
                                 ipv)
                              [ (/\dead -> Unknown)
                              , (/\dead -> Known (Nil {integer})) ]
                              {all dead. dead})
                         {all dead. dead})))
  in
  letrec
    !`$fEqList_$c==` :
       all a. (\a -> a -> a -> bool) a -> List a -> List a -> bool
      = /\a ->
          \(`$dEq` : (\a -> a -> a -> bool) a) (eta : List a) (eta : List a) ->
            List_match
              {a}
              eta
              {all dead. bool}
              (/\dead ->
                 List_match
                   {a}
                   eta
                   {bool}
                   True
                   (\(ipv : a) (ipv : List a) -> False))
              (\(x : a) (xs : List a) ->
                 /\dead ->
                   List_match
                     {a}
                     eta
                     {bool}
                     False
                     (\(y : a) (ys : List a) ->
                        case
                          (all dead. bool)
                          (`$dEq` x y)
                          [ (/\dead -> False)
                          , (/\dead -> `$fEqList_$c==` {a} `$dEq` xs ys) ]
                          {all dead. dead}))
              {all dead. dead}
  in
  let
    !`$c==` : ConflictSet -> ConflictSet -> bool
      = \(ds : ConflictSet) (ds : ConflictSet) ->
          ConflictSet_match
            ds
            {all dead. bool}
            (\(v : List integer) ->
               /\dead ->
                 ConflictSet_match
                   ds
                   {all dead. bool}
                   (\(w : List integer) ->
                      /\dead -> `$fEqList_$c==` {integer} equalsInteger v w)
                   (/\dead -> False)
                   {all dead. dead})
            (/\dead ->
               ConflictSet_match
                 ds
                 {bool}
                 (\(ipv : List integer) -> False)
                 True)
            {all dead. dead}
  in
  letrec
    !interval : integer -> integer -> List integer
      = \(a : integer) (b : integer) ->
          case
            (all dead. List integer)
            (case bool (lessThanEqualsInteger a b) [True, False])
            [ (/\dead -> Cons {integer} a (interval (addInteger 1 a) b))
            , (/\dead -> Nil {integer}) ]
            {all dead. dead}
  in
  let
    !traceError : all a. string -> a
      = /\a ->
          \(str : string) -> let !x : Unit = trace {Unit} str Unit in error {a}
    !zipWith : all a b c. (a -> b -> c) -> List a -> List b -> List c
      = /\a b c ->
          \(f : a -> b -> c) ->
            letrec
              !go : List a -> List b -> List c
                = \(ds : List a) (ds : List b) ->
                    List_match
                      {a}
                      ds
                      {all dead. List c}
                      (/\dead -> Nil {c})
                      (\(ipv : a) (ipv : List a) ->
                         /\dead ->
                           List_match
                             {b}
                             ds
                             {all dead. List c}
                             (/\dead -> Nil {c})
                             (\(ipv : b) (ipv : List b) ->
                                /\dead -> Cons {c} (f ipv ipv) (go ipv ipv))
                             {all dead. dead})
                      {all dead. dead}
            in
            \(eta : List a) (eta : List b) -> go eta eta
  in
  letrec
    !cacheChecks :
       CSP ->
       List (List ConflictSet) ->
       Tree (List Assign) ->
       Tree (Tuple2 (List Assign) (List (List ConflictSet)))
      = \(csp : CSP)
         (tbl : List (List ConflictSet))
         (ds : Tree (List Assign)) ->
          Tree_match
            {List Assign}
            ds
            {Tree (Tuple2 (List Assign) (List (List ConflictSet)))}
            (\(s : List Assign)
              (cs : List (Tree (List Assign))) ->
               (let
                   a = Tuple2 (List Assign) (List (List ConflictSet))
                 in
                 \(conrep : a) (conrep : List (Tree a)) ->
                   Node {a} conrep conrep)
                 (Tuple2 {List Assign} {List (List ConflictSet)} s tbl)
                 (let
                   !f :
                      Tree (List Assign) ->
                      Tree (Tuple2 (List Assign) (List (List ConflictSet)))
                     = cacheChecks
                         csp
                         (let
                           !tbl : List (List ConflictSet)
                             = List_match
                                 {List ConflictSet}
                                 tbl
                                 {all dead. List (List ConflictSet)}
                                 (/\dead ->
                                    traceError {List (List ConflictSet)} "PT9")
                                 (\(ds : List ConflictSet)
                                   (as : List (List ConflictSet)) ->
                                    /\dead -> as)
                                 {all dead. dead}
                         in
                         List_match
                           {Assign}
                           s
                           {all dead. List (List ConflictSet)}
                           (/\dead -> tbl)
                           (\(ds : Assign)
                             (as : List Assign) ->
                              /\dead ->
                                Assign_match
                                  ds
                                  {List (List ConflictSet)}
                                  (\(var' : integer)
                                    (val' : integer) ->
                                     CSP_match
                                       csp
                                       {List (List ConflictSet)}
                                       (\(ds : integer)
                                         (ds : integer)
                                         (ds : Assign -> Assign -> bool) ->
                                          zipWith
                                            {List ConflictSet}
                                            {List (Tuple2 integer integer)}
                                            {List ConflictSet}
                                            (zipWith
                                               {ConflictSet}
                                               {Tuple2 integer integer}
                                               {ConflictSet}
                                               (\(cs : ConflictSet)
                                                 (ds :
                                                    Tuple2 integer integer) ->
                                                  Tuple2_match
                                                    {integer}
                                                    {integer}
                                                    ds
                                                    {ConflictSet}
                                                    (\(var : integer)
                                                      (val : integer) ->
                                                       case
                                                         (all dead. ConflictSet)
                                                         (case
                                                            (all dead. bool)
                                                            (`$c==` cs Unknown)
                                                            [ (/\dead -> False)
                                                            , (/\dead ->
                                                                 case
                                                                   bool
                                                                   (ds
                                                                      ds
                                                                      (`Cons=`
                                                                         var
                                                                         val))
                                                                   [ True
                                                                   , False ]) ]
                                                            {all dead. dead})
                                                         [ (/\dead -> cs)
                                                         , (/\dead ->
                                                              Known
                                                                ((let
                                                                     a
                                                                       = List
                                                                           integer
                                                                   in
                                                                   \(c :
                                                                       integer ->
                                                                       a ->
                                                                       a)
                                                                    (n : a) ->
                                                                     c
                                                                       var'
                                                                       (c
                                                                          var
                                                                          n))
                                                                   (\(ds :
                                                                        integer)
                                                                     (ds :
                                                                        List
                                                                          integer) ->
                                                                      Cons
                                                                        {integer}
                                                                        ds
                                                                        ds)
                                                                   (Nil
                                                                      {integer}))) ]
                                                         {all dead. dead})))
                                            tbl
                                            ((let
                                                 a
                                                   = List
                                                       (Tuple2 integer integer)
                                               in
                                               \(g :
                                                   all b.
                                                     (a -> b -> b) -> b -> b) ->
                                                 g
                                                   {List a}
                                                   (\(ds : a) (ds : List a) ->
                                                      Cons {a} ds ds)
                                                   (Nil {a}))
                                               (/\a ->
                                                  \(c :
                                                      List
                                                        (Tuple2
                                                           integer
                                                           integer) ->
                                                      a ->
                                                      a)
                                                   (n : a) ->
                                                    letrec
                                                      !go :
                                                         List integer -> a
                                                        = \(ds :
                                                              List integer) ->
                                                            List_match
                                                              {integer}
                                                              ds
                                                              {all dead. a}
                                                              (/\dead -> n)
                                                              (\(y : integer)
                                                                (ys :
                                                                   List
                                                                     integer) ->
                                                                 /\dead ->
                                                                   let
                                                                     !ds : a
                                                                       = go ys
                                                                   in
                                                                   c
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
                                                                            {List
                                                                               a}
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
                                                                             letrec
                                                                               !go :
                                                                                  List
                                                                                    integer ->
                                                                                  a
                                                                                 = \(ds :
                                                                                       List
                                                                                         integer) ->
                                                                                     List_match
                                                                                       {integer}
                                                                                       ds
                                                                                       {all dead.
                                                                                          a}
                                                                                       (/\dead ->
                                                                                          n)
                                                                                       (\(y :
                                                                                            integer)
                                                                                         (ys :
                                                                                            List
                                                                                              integer) ->
                                                                                          /\dead ->
                                                                                            let
                                                                                              !ds :
                                                                                                 a
                                                                                                = go
                                                                                                    ys
                                                                                            in
                                                                                            c
                                                                                              (Tuple2
                                                                                                 {integer}
                                                                                                 {integer}
                                                                                                 y
                                                                                                 y)
                                                                                              ds)
                                                                                       {all dead.
                                                                                          dead}
                                                                             in
                                                                             let
                                                                               !eta :
                                                                                  List
                                                                                    integer
                                                                                 = interval
                                                                                     1
                                                                                     ds
                                                                             in
                                                                             go
                                                                               eta))
                                                                     ds)
                                                              {all dead. dead}
                                                    in
                                                    let
                                                      !eta : List integer
                                                        = interval
                                                            (addInteger 1 var')
                                                            ds
                                                    in
                                                    go eta)))))
                           {all dead. dead})
                 in
                 letrec
                   !go :
                      List (Tree (List Assign)) ->
                      List
                        (Tree (Tuple2 (List Assign) (List (List ConflictSet))))
                     = \(ds : List (Tree (List Assign))) ->
                         List_match
                           {Tree (List Assign)}
                           ds
                           {all dead.
                              List
                                (Tree
                                   (Tuple2
                                      (List Assign)
                                      (List (List ConflictSet))))}
                           (/\dead ->
                              Nil
                                {Tree
                                   (Tuple2
                                      (List Assign)
                                      (List (List ConflictSet)))})
                           (\(x : Tree (List Assign))
                             (xs : List (Tree (List Assign))) ->
                              /\dead ->
                                Cons
                                  {Tree
                                     (Tuple2
                                        (List Assign)
                                        (List (List ConflictSet)))}
                                  (f x)
                                  (go xs))
                           {all dead. dead}
                 in
                 go cs))
  in
  letrec
    !collect : List ConflictSet -> List integer
      = \(ds : List ConflictSet) ->
          List_match
            {ConflictSet}
            ds
            {all dead. List integer}
            (/\dead -> Nil {integer})
            (\(ds : ConflictSet) (css : List ConflictSet) ->
               /\dead ->
                 ConflictSet_match
                   ds
                   {all dead. List integer}
                   (\(cs : List integer) ->
                      /\dead ->
                        unionBy {integer} equalsInteger cs (collect css))
                   (/\dead ->
                      let
                        !defaultBody : List integer = error {List integer}
                      in
                      Unit_match (error {Unit}) {List integer} defaultBody)
                   {all dead. dead})
            {all dead. dead}
  in
  let
    !emptyTable : CSP -> List (List ConflictSet)
      = \(ds : CSP) ->
          CSP_match
            ds
            {List (List ConflictSet)}
            (\(ds : integer) (ds : integer) (ds : Assign -> Assign -> bool) ->
               Cons
                 {List ConflictSet}
                 (Nil {ConflictSet})
                 ((let
                      a = List ConflictSet
                    in
                    \(g : all b. (a -> b -> b) -> b -> b) ->
                      g
                        {List a}
                        (\(ds : a) (ds : List a) -> Cons {a} ds ds)
                        (Nil {a}))
                    (/\a ->
                       \(c : List ConflictSet -> a -> a) (n : a) ->
                         letrec
                           !go : List integer -> a
                             = \(ds : List integer) ->
                                 List_match
                                   {integer}
                                   ds
                                   {all dead. a}
                                   (/\dead -> n)
                                   (\(y : integer) (ys : List integer) ->
                                      /\dead ->
                                        let
                                          !ds : a = go ys
                                        in
                                        c
                                          ((let
                                               a = List ConflictSet
                                             in
                                             \(c : ConflictSet -> a -> a)
                                              (n : a) ->
                                               letrec
                                                 !go : List integer -> a
                                                   = \(ds : List integer) ->
                                                       List_match
                                                         {integer}
                                                         ds
                                                         {all dead. a}
                                                         (/\dead -> n)
                                                         (\(y : integer)
                                                           (ys :
                                                              List integer) ->
                                                            /\dead ->
                                                              let
                                                                !ds : a = go ys
                                                              in
                                                              c Unknown ds)
                                                         {all dead. dead}
                                               in
                                               let
                                                 !eta : List integer
                                                   = interval 1 ds
                                               in
                                               go eta)
                                             (\(ds : ConflictSet)
                                               (ds : List ConflictSet) ->
                                                Cons {ConflictSet} ds ds)
                                             (Nil {ConflictSet}))
                                          ds)
                                   {all dead. dead}
                         in
                         let
                           !eta : List integer = interval 1 ds
                         in
                         go eta)))
  in
  letrec
    !go : integer -> List ConflictSet -> ConflictSet
      = \(ds : integer) (ds : List ConflictSet) ->
          List_match
            {ConflictSet}
            ds
            {all dead. ConflictSet}
            (/\dead -> traceError {ConflictSet} "PT7")
            (\(x : ConflictSet) (xs : List ConflictSet) ->
               /\dead ->
                 case
                   (all dead. ConflictSet)
                   (equalsInteger 0 ds)
                   [(/\dead -> go (subtractInteger ds 1) xs), (/\dead -> x)]
                   {all dead. dead})
            {all dead. dead}
  in
  let
    !lookupCache :
       CSP ->
       Tree (Tuple2 (List Assign) (List (List ConflictSet))) ->
       Tree
         (Tuple2 (Tuple2 (List Assign) ConflictSet) (List (List ConflictSet)))
      = \(csp : CSP)
         (t : Tree (Tuple2 (List Assign) (List (List ConflictSet)))) ->
          CSP_match
            csp
            {Tree
               (Tuple2
                  (Tuple2 (List Assign) ConflictSet)
                  (List (List ConflictSet)))}
            (\(ipv : integer)
              (ipv : integer)
              (ipv : Assign -> Assign -> bool) ->
               mapTree
                 {Tuple2 (List Assign) (List (List ConflictSet))}
                 {Tuple2
                    (Tuple2 (List Assign) ConflictSet)
                    (List (List ConflictSet))}
                 (\(ds : Tuple2 (List Assign) (List (List ConflictSet))) ->
                    Tuple2_match
                      {List Assign}
                      {List (List ConflictSet)}
                      ds
                      {Tuple2
                         (Tuple2 (List Assign) ConflictSet)
                         (List (List ConflictSet))}
                      (\(ds : List Assign) (tbl : List (List ConflictSet)) ->
                         List_match
                           {Assign}
                           ds
                           {all dead.
                              Tuple2
                                (Tuple2 (List Assign) ConflictSet)
                                (List (List ConflictSet))}
                           (/\dead ->
                              Tuple2
                                {Tuple2 (List Assign) ConflictSet}
                                {List (List ConflictSet)}
                                (Tuple2
                                   {List Assign}
                                   {ConflictSet}
                                   (Nil {Assign})
                                   Unknown)
                                tbl)
                           (\(a : Assign) (ds : List Assign) ->
                              /\dead ->
                                let
                                  !tableEntry : ConflictSet
                                    = let
                                      !ds : List ConflictSet
                                        = List_match
                                            {List ConflictSet}
                                            tbl
                                            {all dead. List ConflictSet}
                                            (/\dead ->
                                               traceError
                                                 {List ConflictSet}
                                                 "PT8")
                                            (\(x : List ConflictSet)
                                              (ds : List (List ConflictSet)) ->
                                               /\dead -> x)
                                            {all dead. dead}
                                      !n : integer
                                        = subtractInteger
                                            (Assign_match
                                               a
                                               {integer}
                                               (\(var : integer)
                                                 (val : integer) ->
                                                  val))
                                            1
                                    in
                                    case
                                      (all dead. ConflictSet)
                                      (lessThanInteger n 0)
                                      [ (/\dead -> go n ds)
                                      , (/\dead ->
                                           traceError {ConflictSet} "PT6") ]
                                      {all dead. dead}
                                in
                                Tuple2
                                  {Tuple2 (List Assign) ConflictSet}
                                  {List (List ConflictSet)}
                                  (Tuple2
                                     {List Assign}
                                     {ConflictSet}
                                     ds
                                     (case
                                        (all dead. ConflictSet)
                                        (`$c==` tableEntry Unknown)
                                        [ (/\dead -> tableEntry)
                                        , (/\dead ->
                                             case
                                               (all dead. ConflictSet)
                                               (equalsInteger
                                                  (Assign_match
                                                     a
                                                     {integer}
                                                     (\(var : integer)
                                                       (val : integer) ->
                                                        var))
                                                  ipv)
                                               [ (/\dead -> Unknown)
                                               , (/\dead ->
                                                    Known (Nil {integer})) ]
                                               {all dead. dead}) ]
                                        {all dead. dead}))
                                  tbl)
                           {all dead. dead}))
                 t)
  in
  letrec
    !foldTree : all a b. (a -> List b -> b) -> Tree a -> b
      = /\a b ->
          \(f : a -> List b -> b) (ds : Tree a) ->
            Tree_match
              {a}
              ds
              {b}
              (\(a : a) (cs : List (Tree a)) ->
                 f
                   a
                   (let
                     !f : Tree a -> b = foldTree {a} {b} f
                   in
                   letrec
                     !go : List (Tree a) -> List b
                       = \(ds : List (Tree a)) ->
                           List_match
                             {Tree a}
                             ds
                             {all dead. List b}
                             (/\dead -> Nil {b})
                             (\(x : Tree a) (xs : List (Tree a)) ->
                                /\dead -> Cons {b} (f x) (go xs))
                             {all dead. dead}
                   in
                   go cs))
  in
  letrec
    !leaves : all a. Tree a -> List a
      = /\a ->
          letrec
            !go : List (List a) -> List a
              = \(ds : List (List a)) ->
                  List_match
                    {List a}
                    ds
                    {all dead. List a}
                    (/\dead -> Nil {a})
                    (\(x : List a) (xs : List (List a)) ->
                       /\dead ->
                         let
                           !r : List a = go xs
                         in
                         letrec
                           !go : List a -> List a
                             = \(ds : List a) ->
                                 List_match
                                   {a}
                                   ds
                                   {all dead. List a}
                                   (/\dead -> r)
                                   (\(x : a) (xs : List a) ->
                                      /\dead -> Cons {a} x (go xs))
                                   {all dead. dead}
                         in
                         go x)
                    {all dead. dead}
          in
          letrec
            !go : List (Tree a) -> List (List a)
              = \(ds : List (Tree a)) ->
                  List_match
                    {Tree a}
                    ds
                    {all dead. List (List a)}
                    (/\dead -> Nil {List a})
                    (\(x : Tree a) (xs : List (Tree a)) ->
                       /\dead -> Cons {List a} (leaves {a} x) (go xs))
                    {all dead. dead}
          in
          \(ds : Tree a) ->
            Tree_match
              {a}
              ds
              {List a}
              (\(leaf : a) (ds : List (Tree a)) ->
                 List_match
                   {Tree a}
                   ds
                   {all dead. List a}
                   (/\dead ->
                      (let
                          a = List a
                        in
                        \(c : a -> a -> a) (n : a) -> c leaf n)
                        (\(ds : a) (ds : List a) -> Cons {a} ds ds)
                        (Nil {a}))
                   (\(ipv : Tree a) (ipv : List (Tree a)) ->
                      /\dead -> let !eta : List (List a) = go ds in go eta)
                   {all dead. dead})
  in
  letrec
    !initTree : all a. (a -> List a) -> a -> Tree a
      = /\a ->
          \(f : a -> List a) (a : a) ->
            Node
              {a}
              a
              (let
                !f : a -> Tree a = initTree {a} f
              in
              letrec
                !go : List a -> List (Tree a)
                  = \(ds : List a) ->
                      List_match
                        {a}
                        ds
                        {all dead. List (Tree a)}
                        (/\dead -> Nil {Tree a})
                        (\(x : a) (xs : List a) ->
                           /\dead -> Cons {Tree a} (f x) (go xs))
                        {all dead. dead}
              in
              go (f a))
  in
  \(n : integer) ->
    let
      !csp : CSP
        = CSP
            n
            n
            (\(ds : Assign) (ds : Assign) ->
               Assign_match
                 ds
                 {bool}
                 (\(i : integer) (m : integer) ->
                    Assign_match
                      ds
                      {bool}
                      (\(j : integer) (n : integer) ->
                         case
                           (all dead. bool)
                           (case bool (equalsInteger m n) [True, False])
                           [ (/\dead -> False)
                           , (/\dead ->
                                case
                                  bool
                                  (equalsInteger
                                     (let
                                       !n : integer = subtractInteger i j
                                     in
                                     case
                                       (all dead. integer)
                                       (lessThanInteger n 0)
                                       [ (/\dead -> n)
                                       , (/\dead -> subtractInteger 0 n) ]
                                       {all dead. dead})
                                     (let
                                       !n : integer = subtractInteger m n
                                     in
                                     case
                                       (all dead. integer)
                                       (lessThanInteger n 0)
                                       [ (/\dead -> n)
                                       , (/\dead -> subtractInteger 0 n) ]
                                       {all dead. dead}))
                                  [True, False]) ]
                           {all dead. dead})))
    in
    \(alg : Algorithm) ->
      let
        !labeler :
           CSP -> Tree (List Assign) -> Tree (Tuple2 (List Assign) ConflictSet)
          = Algorithm_match
              alg
              {all dead.
                 CSP ->
                 Tree (List Assign) ->
                 Tree (Tuple2 (List Assign) ConflictSet)}
              (/\dead ->
                 \(csp : CSP) (eta : Tree (List Assign)) ->
                   foldTree
                     {Tuple2 (List Assign) ConflictSet}
                     {Tree (Tuple2 (List Assign) ConflictSet)}
                     (\(ds : Tuple2 (List Assign) ConflictSet)
                       (chs : List (Tree (Tuple2 (List Assign) ConflictSet))) ->
                        Tuple2_match
                          {List Assign}
                          {ConflictSet}
                          ds
                          {Tree (Tuple2 (List Assign) ConflictSet)}
                          (\(a : List Assign) (ds : ConflictSet) ->
                             ConflictSet_match
                               ds
                               {all dead.
                                  Tree (Tuple2 (List Assign) ConflictSet)}
                               (\(cs : List integer) ->
                                  /\dead ->
                                    (let
                                        a = Tuple2 (List Assign) ConflictSet
                                      in
                                      \(conrep : a) (conrep : List (Tree a)) ->
                                        Node {a} conrep conrep)
                                      (Tuple2
                                         {List Assign}
                                         {ConflictSet}
                                         a
                                         (Known cs))
                                      chs)
                               (/\dead ->
                                  (let
                                      a = Tuple2 (List Assign) ConflictSet
                                    in
                                    \(conrep : a) (conrep : List (Tree a)) ->
                                      Node {a} conrep conrep)
                                    (Tuple2
                                       {List Assign}
                                       {ConflictSet}
                                       a
                                       (Known
                                          (combine (go chs) (Nil {integer}))))
                                    chs)
                               {all dead. dead}))
                     (bt csp eta))
              (/\dead ->
                 \(csp : CSP) (eta : Tree (List Assign)) ->
                   foldTree
                     {Tuple2 (List Assign) ConflictSet}
                     {Tree (Tuple2 (List Assign) ConflictSet)}
                     (\(ds : Tuple2 (List Assign) ConflictSet)
                       (chs : List (Tree (Tuple2 (List Assign) ConflictSet))) ->
                        Tuple2_match
                          {List Assign}
                          {ConflictSet}
                          ds
                          {Tree (Tuple2 (List Assign) ConflictSet)}
                          (\(a : List Assign) (ds : ConflictSet) ->
                             ConflictSet_match
                               ds
                               {all dead.
                                  Tree (Tuple2 (List Assign) ConflictSet)}
                               (\(cs : List integer) ->
                                  /\dead ->
                                    (let
                                        a = Tuple2 (List Assign) ConflictSet
                                      in
                                      \(conrep : a) (conrep : List (Tree a)) ->
                                        Node {a} conrep conrep)
                                      (Tuple2
                                         {List Assign}
                                         {ConflictSet}
                                         a
                                         (Known cs))
                                      chs)
                               (/\dead ->
                                  let
                                    !conrep : List integer
                                      = combine (go chs) (Nil {integer})
                                    !cs' : ConflictSet = Known conrep
                                  in
                                  case
                                    (all dead.
                                       Tree (Tuple2 (List Assign) ConflictSet))
                                    (List_match
                                       {integer}
                                       conrep
                                       {bool}
                                       False
                                       (\(a : integer) (as : List integer) ->
                                          True))
                                    [ (/\dead ->
                                         (let
                                             a
                                               = Tuple2
                                                   (List Assign)
                                                   ConflictSet
                                           in
                                           \(conrep : a)
                                            (conrep : List (Tree a)) ->
                                             Node {a} conrep conrep)
                                           (Tuple2
                                              {List Assign}
                                              {ConflictSet}
                                              a
                                              cs')
                                           chs)
                                    , (/\dead ->
                                         (let
                                             a
                                               = Tuple2
                                                   (List Assign)
                                                   ConflictSet
                                           in
                                           \(conrep : a)
                                            (conrep : List (Tree a)) ->
                                             Node {a} conrep conrep)
                                           (Tuple2
                                              {List Assign}
                                              {ConflictSet}
                                              a
                                              cs')
                                           (Nil
                                              {Tree
                                                 (Tuple2
                                                    (List Assign)
                                                    ConflictSet)})) ]
                                    {all dead. dead})
                               {all dead. dead}))
                     (bt csp eta))
              (/\dead ->
                 \(csp : CSP) (eta : Tree (List Assign)) ->
                   mapTree
                     {Tuple2
                        (Tuple2 (List Assign) ConflictSet)
                        (List (List ConflictSet))}
                     {Tuple2 (List Assign) ConflictSet}
                     ((let
                          a = Tuple2 (List Assign) ConflictSet
                        in
                        /\b ->
                          \(ds : Tuple2 a b) ->
                            Tuple2_match
                              {a}
                              {b}
                              ds
                              {a}
                              (\(a : a) (ds : b) -> a))
                        {List (List ConflictSet)})
                     (lookupCache csp (cacheChecks csp (emptyTable csp) eta)))
              (/\dead -> bt)
              (/\dead ->
                 \(csp : CSP) (eta : Tree (List Assign)) ->
                   let
                     !t :
                        Tree
                          (Tuple2
                             (Tuple2 (List Assign) ConflictSet)
                             (List (List ConflictSet)))
                       = lookupCache csp (cacheChecks csp (emptyTable csp) eta)
                   in
                   mapTree
                     {Tuple2
                        (Tuple2 (List Assign) ConflictSet)
                        (List (List ConflictSet))}
                     {Tuple2 (List Assign) ConflictSet}
                     (\(ds :
                          Tuple2
                            (Tuple2 (List Assign) ConflictSet)
                            (List (List ConflictSet))) ->
                        Tuple2_match
                          {Tuple2 (List Assign) ConflictSet}
                          {List (List ConflictSet)}
                          ds
                          {Tuple2 (List Assign) ConflictSet}
                          (\(ds : Tuple2 (List Assign) ConflictSet)
                            (tbl : List (List ConflictSet)) ->
                             Tuple2_match
                               {List Assign}
                               {ConflictSet}
                               ds
                               {Tuple2 (List Assign) ConflictSet}
                               (\(as : List Assign) (cs : ConflictSet) ->
                                  let
                                    !wipedDomains : List (List ConflictSet)
                                      = (let
                                            a = List ConflictSet
                                          in
                                          \(g :
                                              all b. (a -> b -> b) -> b -> b) ->
                                            g
                                              {List a}
                                              (\(ds : a) (ds : List a) ->
                                                 Cons {a} ds ds)
                                              (Nil {a}))
                                          (/\a ->
                                             \(c : List ConflictSet -> a -> a)
                                              (n : a) ->
                                               (let
                                                   a = List ConflictSet
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
                                                               (\(y : a)
                                                                 (ys :
                                                                    List a) ->
                                                                  /\dead ->
                                                                    k y (go ys))
                                                               {all dead. dead}
                                                     in
                                                     \(eta : List a) -> go eta)
                                                 {a}
                                                 (\(ds : List ConflictSet)
                                                   (ds : a) ->
                                                    case
                                                      (all dead. a)
                                                      (go ds)
                                                      [ (/\dead -> ds)
                                                      , (/\dead -> c ds ds) ]
                                                      {all dead. dead})
                                                 n
                                                 tbl)
                                  in
                                  Tuple2
                                    {List Assign}
                                    {ConflictSet}
                                    as
                                    (case
                                       (all dead. ConflictSet)
                                       (List_match
                                          {List ConflictSet}
                                          wipedDomains
                                          {bool}
                                          True
                                          (\(ipv : List ConflictSet)
                                            (ipv : List (List ConflictSet)) ->
                                             False))
                                       [ (/\dead ->
                                            Known
                                              (collect
                                                 (List_match
                                                    {List ConflictSet}
                                                    wipedDomains
                                                    {all dead. List ConflictSet}
                                                    (/\dead ->
                                                       traceError
                                                         {List ConflictSet}
                                                         "PT8")
                                                    (\(x : List ConflictSet)
                                                      (ds :
                                                         List
                                                           (List
                                                              ConflictSet)) ->
                                                       /\dead -> x)
                                                    {all dead. dead})))
                                       , (/\dead -> cs) ]
                                       {all dead. dead}))))
                     t)
              {all dead. dead}
      in
      go
        (filter
           {Tuple2 (List Assign) ConflictSet}
           (\(eta : Tuple2 (List Assign) ConflictSet) ->
              Tuple2_match
                {List Assign}
                {ConflictSet}
                eta
                {bool}
                (\(ipv : List Assign) (ipv : ConflictSet) ->
                   ConflictSet_match
                     ipv
                     {bool}
                     (\(ds : List integer) ->
                        List_match
                          {integer}
                          ds
                          {bool}
                          True
                          (\(ipv : integer) (ipv : List integer) -> False))
                     False))
           (leaves
              {Tuple2 (List Assign) ConflictSet}
              (foldTree
                 {Tuple2 (List Assign) ConflictSet}
                 {Tree (Tuple2 (List Assign) ConflictSet)}
                 (\(a : Tuple2 (List Assign) ConflictSet)
                   (cs : List (Tree (Tuple2 (List Assign) ConflictSet))) ->
                    (let
                        a = Tuple2 (List Assign) ConflictSet
                      in
                      \(conrep : a) (conrep : List (Tree a)) ->
                        Node {a} conrep conrep)
                      a
                      (filter
                         {Tree (Tuple2 (List Assign) ConflictSet)}
                         (\(eta : Tree (Tuple2 (List Assign) ConflictSet)) ->
                            Tree_match
                              {Tuple2 (List Assign) ConflictSet}
                              eta
                              {bool}
                              (\(ipv : Tuple2 (List Assign) ConflictSet)
                                (ipv :
                                   List
                                     (Tree
                                        (Tuple2 (List Assign) ConflictSet))) ->
                                 Tuple2_match
                                   {List Assign}
                                   {ConflictSet}
                                   ipv
                                   {bool}
                                   (\(ipv : List Assign) (ipv : ConflictSet) ->
                                      case
                                        bool
                                        (ConflictSet_match
                                           ipv
                                           {bool}
                                           (\(ds : List integer) ->
                                              List_match
                                                {integer}
                                                ds
                                                {bool}
                                                False
                                                (\(a : integer)
                                                  (as : List integer) ->
                                                   True))
                                           False)
                                        [True, False])))
                         cs))
                 (labeler
                    csp
                    (CSP_match
                       csp
                       {Tree (List Assign)}
                       (\(ds : integer)
                         (ds : integer)
                         (ds : Assign -> Assign -> bool) ->
                          let
                            !vallist : List integer = interval 1 ds
                          in
                          initTree
                            {List Assign}
                            (\(ss : List Assign) ->
                               (let
                                   a = List Assign
                                 in
                                 \(g : all b. (a -> b -> b) -> b -> b) ->
                                   g
                                     {List a}
                                     (\(ds : a) (ds : List a) -> Cons {a} ds ds)
                                     (Nil {a}))
                                 (/\a ->
                                    \(c : List Assign -> a -> a)
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
                                                     c
                                                       (Cons
                                                          {Assign}
                                                          (`Cons=`
                                                             (addInteger
                                                                1
                                                                (List_match
                                                                   {Assign}
                                                                   ss
                                                                   {integer}
                                                                   0
                                                                   (\(ds :
                                                                        Assign)
                                                                     (ds :
                                                                        List
                                                                          Assign) ->
                                                                      Assign_match
                                                                        ds
                                                                        {integer}
                                                                        (\(var :
                                                                             integer)
                                                                          (val :
                                                                             integer) ->
                                                                           var))))
                                                             y)
                                                          ss)
                                                       ds)
                                                {all dead. dead}
                                      in
                                      case
                                        (all dead. a)
                                        (lessThanInteger
                                           (List_match
                                              {Assign}
                                              ss
                                              {integer}
                                              0
                                              (\(ds : Assign)
                                                (ds : List Assign) ->
                                                 Assign_match
                                                   ds
                                                   {integer}
                                                   (\(var : integer)
                                                     (val : integer) ->
                                                      var)))
                                           ds)
                                        [(/\dead -> n), (/\dead -> go vallist)]
                                        {all dead. dead}))
                            (Nil {Assign}))))))))
  5
  (let
    data `PlutusBenchmark.NoFib.Queens.Algorithm` | `match_PlutusBenchmark.NoFib.Queens.Algorithm` where
      `PlutusBenchmark.NoFib.Queens.Bjbt1` :
        `PlutusBenchmark.NoFib.Queens.Algorithm`
      `PlutusBenchmark.NoFib.Queens.Bjbt2` :
        `PlutusBenchmark.NoFib.Queens.Algorithm`
      `PlutusBenchmark.NoFib.Queens.Bm` :
        `PlutusBenchmark.NoFib.Queens.Algorithm`
      `PlutusBenchmark.NoFib.Queens.Bt` :
        `PlutusBenchmark.NoFib.Queens.Algorithm`
      `PlutusBenchmark.NoFib.Queens.Fc` :
        `PlutusBenchmark.NoFib.Queens.Algorithm`
  in
  `PlutusBenchmark.NoFib.Queens.Fc`)