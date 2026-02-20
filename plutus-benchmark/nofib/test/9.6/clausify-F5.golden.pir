(let
    data Unit | Unit_match where
      Unit : Unit
    data (Tuple2 :: * -> * -> *) a b | Tuple2_match where
      Tuple2 : a -> b -> Tuple2 a b
  in
  letrec
    data (List :: * -> *) a | List_match where
      Nil : List a
      Cons : a -> List a -> List a
  in
  let
    !fail : unit -> Tuple2 (List integer) (List integer)
      = \(ds : unit) ->
          let
            !defaultBody : Tuple2 (List integer) (List integer)
              = error {Tuple2 (List integer) (List integer)}
          in
          Unit_match
            (error {Unit})
            {Tuple2 (List integer) (List integer)}
            defaultBody
    ~defaultBody : Tuple2 (List integer) (List integer) = fail ()
    ~defaultBody : Tuple2 (List integer) (List integer) = fail ()
    !ifThenElse : all a. bool -> a -> a -> a
      = /\a -> \(b : bool) (x : a) (y : a) -> case a b [y, x]
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
    !equalsInteger : integer -> integer -> bool
      = \(x : integer) (y : integer) -> equalsInteger x y
    !`$fOrdInteger` : Ord integer
      = CConsOrd
          {integer}
          equalsInteger
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
    data Formula | Formula_match where
      Con : Formula -> Formula -> Formula
      Dis : Formula -> Formula -> Formula
      Eqv : Formula -> Formula -> Formula
      Imp : Formula -> Formula -> Formula
      Not : Formula -> Formula
      Sym : integer -> Formula
  in
  letrec
    !insert : all t. Ord t -> t -> List t -> List t
      = /\t ->
          \(`$dOrd` : Ord t) (x : t) (ds : List t) ->
            List_match
              {t}
              ds
              {all dead. List t}
              (/\dead ->
                 (let
                     a = List t
                   in
                   \(c : t -> a -> a) (n : a) -> c x n)
                   (\(ds : t) (ds : List t) -> Cons {t} ds ds)
                   (Nil {t}))
              (\(y : t) (ys : List t) ->
                 /\dead ->
                   case
                     (all dead. List t)
                     (Ord_match
                        {t}
                        `$dOrd`
                        {t -> t -> bool}
                        (\(v : (\a -> a -> a -> bool) t)
                          (v : t -> t -> Ordering)
                          (v : t -> t -> bool)
                          (v : t -> t -> bool)
                          (v : t -> t -> bool)
                          (v : t -> t -> bool)
                          (v : t -> t -> t)
                          (v : t -> t -> t) ->
                           v)
                        x
                        y)
                     [ (/\dead ->
                          case
                            (all dead. List t)
                            (Ord_match
                               {t}
                               `$dOrd`
                               {t -> t -> bool}
                               (\(v : (\a -> a -> a -> bool) t)
                                 (v : t -> t -> Ordering)
                                 (v : t -> t -> bool)
                                 (v : t -> t -> bool)
                                 (v : t -> t -> bool)
                                 (v : t -> t -> bool)
                                 (v : t -> t -> t)
                                 (v : t -> t -> t) ->
                                  v)
                               x
                               y)
                            [ (/\dead -> ds)
                            , (/\dead -> Cons {t} y (insert {t} `$dOrd` x ys)) ]
                            {all dead. dead})
                     , (/\dead -> Cons {t} x ds) ]
                     {all dead. dead})
              {all dead. dead}
  in
  letrec
    !clause' :
       Formula ->
       Tuple2 (List integer) (List integer) ->
       Tuple2 (List integer) (List integer)
      = \(ds : Formula) (x : Tuple2 (List integer) (List integer)) ->
          Formula_match
            ds
            {Tuple2 (List integer) (List integer)}
            (\(default_arg0 : Formula) (default_arg1 : Formula) -> defaultBody)
            (\(p : Formula) (q : Formula) -> clause' p (clause' q x))
            (\(default_arg0 : Formula) (default_arg1 : Formula) -> defaultBody)
            (\(default_arg0 : Formula) (default_arg1 : Formula) -> defaultBody)
            (\(ds : Formula) ->
               Formula_match
                 ds
                 {Tuple2 (List integer) (List integer)}
                 (\(default_arg0 : Formula) (default_arg1 : Formula) ->
                    defaultBody)
                 (\(default_arg0 : Formula) (default_arg1 : Formula) ->
                    defaultBody)
                 (\(default_arg0 : Formula) (default_arg1 : Formula) ->
                    defaultBody)
                 (\(default_arg0 : Formula) (default_arg1 : Formula) ->
                    defaultBody)
                 (\(default_arg0 : Formula) -> defaultBody)
                 (\(s : integer) ->
                    Tuple2_match
                      {List integer}
                      {List integer}
                      x
                      {Tuple2 (List integer) (List integer)}
                      (\(c : List integer) (a : List integer) ->
                         Tuple2
                           {List integer}
                           {List integer}
                           c
                           (insert {integer} `$fOrdInteger` s a))))
            (\(s : integer) ->
               Tuple2_match
                 {List integer}
                 {List integer}
                 x
                 {Tuple2 (List integer) (List integer)}
                 (\(c : List integer) (a : List integer) ->
                    Tuple2
                      {List integer}
                      {List integer}
                      (insert {integer} `$fOrdInteger` s c)
                      a))
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
    !`$fOrdList_$ccompare` : all a. Ord a -> List a -> List a -> Ordering
      = /\a ->
          \(`$dOrd` : Ord a) (ds : List a) (ds : List a) ->
            List_match
              {a}
              ds
              {all dead. Ordering}
              (/\dead ->
                 List_match
                   {a}
                   ds
                   {all dead. Ordering}
                   (/\dead -> EQ)
                   (\(ds : a) (ds : List a) -> /\dead -> LT)
                   {all dead. dead})
              (\(ds : a) (ds : List a) ->
                 /\dead ->
                   List_match
                     {a}
                     ds
                     {all dead. Ordering}
                     (/\dead -> GT)
                     (\(y : a) ->
                        let
                          ~defaultBody : Ordering = compare {a} `$dOrd` ds y
                        in
                        \(ys : List a) ->
                          /\dead ->
                            Ordering_match
                              (compare {a} `$dOrd` ds y)
                              {all dead. Ordering}
                              (/\dead ->
                                 `$fOrdList_$ccompare` {a} `$dOrd` ds ys)
                              (/\dead -> defaultBody)
                              (/\dead -> defaultBody)
                              {all dead. dead})
                     {all dead. dead})
              {all dead. dead}
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
              (\(l1l : a) (l2l : List a) ->
                 /\dead ->
                   List_match
                     {a}
                     eta
                     {bool}
                     False
                     (\(r1r : a) (r2r : List a) ->
                        case
                          (all dead. bool)
                          (`$dEq` l1l r1r)
                          [ (/\dead -> False)
                          , (/\dead -> `$fEqList_$c==` {a} `$dEq` l2l r2r) ]
                          {all dead. dead}))
              {all dead. dead}
  in
  let
    ~`$dOrd` : Ord (List integer)
      = CConsOrd
          {List integer}
          (\(eta : List integer) (eta : List integer) ->
             `$fEqList_$c==`
               {integer}
               (`$p1Ord` {integer} `$fOrdInteger`)
               eta
               eta)
          (`$fOrdList_$ccompare` {integer} `$fOrdInteger`)
          (\(x : List integer) (y : List integer) ->
             Ordering_match
               (`$fOrdList_$ccompare` {integer} `$fOrdInteger` x y)
               {all dead. bool}
               (/\dead -> False)
               (/\dead -> False)
               (/\dead -> True)
               {all dead. dead})
          (\(x : List integer) (y : List integer) ->
             Ordering_match
               (`$fOrdList_$ccompare` {integer} `$fOrdInteger` x y)
               {all dead. bool}
               (/\dead -> True)
               (/\dead -> False)
               (/\dead -> True)
               {all dead. dead})
          (\(x : List integer) (y : List integer) ->
             Ordering_match
               (`$fOrdList_$ccompare` {integer} `$fOrdInteger` x y)
               {all dead. bool}
               (/\dead -> False)
               (/\dead -> True)
               (/\dead -> False)
               {all dead. dead})
          (\(x : List integer) (y : List integer) ->
             Ordering_match
               (`$fOrdList_$ccompare` {integer} `$fOrdInteger` x y)
               {all dead. bool}
               (/\dead -> True)
               (/\dead -> True)
               (/\dead -> False)
               {all dead. dead})
          (\(x : List integer) (y : List integer) ->
             Ordering_match
               (`$fOrdList_$ccompare` {integer} `$fOrdInteger` x y)
               {all dead. List integer}
               (/\dead -> y)
               (/\dead -> x)
               (/\dead -> y)
               {all dead. dead})
          (\(x : List integer) (y : List integer) ->
             Ordering_match
               (`$fOrdList_$ccompare` {integer} `$fOrdInteger` x y)
               {all dead. List integer}
               (/\dead -> x)
               (/\dead -> y)
               (/\dead -> x)
               {all dead. dead})
  in
  letrec
    !go : List Formula -> List (Tuple2 (List integer) (List integer))
      = \(ds : List Formula) ->
          List_match
            {Formula}
            ds
            {all dead. List (Tuple2 (List integer) (List integer))}
            (/\dead -> Nil {Tuple2 (List integer) (List integer)})
            (\(x : Formula) (xs : List Formula) ->
               /\dead ->
                 let
                   !x : List (Tuple2 (List integer) (List integer)) = go xs
                   !cp : Tuple2 (List integer) (List integer)
                     = clause'
                         x
                         (Tuple2
                            {List integer}
                            {List integer}
                            (Nil {integer})
                            (Nil {integer}))
                 in
                 case
                   (all dead. List (Tuple2 (List integer) (List integer)))
                   (Tuple2_match
                      {List integer}
                      {List integer}
                      cp
                      {bool}
                      (\(c : List integer) (a : List integer) ->
                         let
                           !x : List integer
                             = (let
                                   a = List integer
                                 in
                                 \(c : integer -> a -> a) (n : a) ->
                                   letrec
                                     !go : List integer -> a
                                       = \(ds : List integer) ->
                                           List_match
                                             {integer}
                                             ds
                                             {all dead. a}
                                             (/\dead -> n)
                                             (\(y : integer) ->
                                                letrec
                                                  !go : List integer -> bool
                                                    = \(ds : List integer) ->
                                                        List_match
                                                          {integer}
                                                          ds
                                                          {bool}
                                                          False
                                                          (\(x : integer)
                                                            (xs :
                                                               List integer) ->
                                                             case
                                                               (all dead. bool)
                                                               (equalsInteger
                                                                  y
                                                                  x)
                                                               [ (/\dead ->
                                                                    go xs)
                                                               , (/\dead ->
                                                                    True) ]
                                                               {all dead. dead})
                                                in
                                                \(ys : List integer) ->
                                                  /\dead ->
                                                    let
                                                      !ds : a = go ys
                                                    in
                                                    case
                                                      (all dead. a)
                                                      (go a)
                                                      [ (/\dead -> ds)
                                                      , (/\dead -> c y ds) ]
                                                      {all dead. dead})
                                             {all dead. dead}
                                   in
                                   go c)
                                 (\(ds : integer) (ds : List integer) ->
                                    Cons {integer} ds ds)
                                 (Nil {integer})
                         in
                         case
                           bool
                           (`$fEqList_$c==`
                              {integer}
                              equalsInteger
                              x
                              (Nil {integer}))
                           [True, False]))
                   [ (/\dead ->
                        insert
                          {Tuple2 (List integer) (List integer)}
                          ((let
                               a = List integer
                             in
                             /\b ->
                               \(v : Ord a) (v : Ord b) ->
                                 CConsOrd
                                   {Tuple2 a b}
                                   (\(eta : Tuple2 a b) (eta : Tuple2 a b) ->
                                      Tuple2_match
                                        {a}
                                        {b}
                                        eta
                                        {bool}
                                        (\(l1l : a) (l2l : b) ->
                                           Tuple2_match
                                             {a}
                                             {b}
                                             eta
                                             {bool}
                                             (\(r1r : a) (r2r : b) ->
                                                case
                                                  (all dead. bool)
                                                  (`$p1Ord` {a} v l1l r1r)
                                                  [ (/\dead -> False)
                                                  , (/\dead ->
                                                       `$p1Ord` {b} v l2l r2r) ]
                                                  {all dead. dead})))
                                   (\(ds : Tuple2 a b) (ds : Tuple2 a b) ->
                                      Tuple2_match
                                        {a}
                                        {b}
                                        ds
                                        {Ordering}
                                        (\(a : a) (b : b) ->
                                           Tuple2_match
                                             {a}
                                             {b}
                                             ds
                                             {Ordering}
                                             (\(a' : a) ->
                                                let
                                                  ~defaultBody : Ordering
                                                    = compare {a} v a a'
                                                in
                                                \(b' : b) ->
                                                  Ordering_match
                                                    (compare {a} v a a')
                                                    {all dead. Ordering}
                                                    (/\dead ->
                                                       compare {b} v b b')
                                                    (/\dead -> defaultBody)
                                                    (/\dead -> defaultBody)
                                                    {all dead. dead})))
                                   (\(x : Tuple2 a b) (y : Tuple2 a b) ->
                                      Tuple2_match
                                        {a}
                                        {b}
                                        x
                                        {bool}
                                        (\(ipv : a) (ipv : b) ->
                                           Tuple2_match
                                             {a}
                                             {b}
                                             y
                                             {bool}
                                             (\(ipv : a) (ipv : b) ->
                                                Ordering_match
                                                  (compare {a} v ipv ipv)
                                                  {all dead. bool}
                                                  (/\dead ->
                                                     Ordering_match
                                                       (compare {b} v ipv ipv)
                                                       {all dead. bool}
                                                       (/\dead -> False)
                                                       (/\dead -> False)
                                                       (/\dead -> True)
                                                       {all dead. dead})
                                                  (/\dead -> False)
                                                  (/\dead -> True)
                                                  {all dead. dead})))
                                   (\(x : Tuple2 a b) (y : Tuple2 a b) ->
                                      Tuple2_match
                                        {a}
                                        {b}
                                        x
                                        {bool}
                                        (\(ipv : a) (ipv : b) ->
                                           Tuple2_match
                                             {a}
                                             {b}
                                             y
                                             {bool}
                                             (\(ipv : a) (ipv : b) ->
                                                Ordering_match
                                                  (compare {a} v ipv ipv)
                                                  {all dead. bool}
                                                  (/\dead ->
                                                     Ordering_match
                                                       (compare {b} v ipv ipv)
                                                       {all dead. bool}
                                                       (/\dead -> True)
                                                       (/\dead -> False)
                                                       (/\dead -> True)
                                                       {all dead. dead})
                                                  (/\dead -> False)
                                                  (/\dead -> True)
                                                  {all dead. dead})))
                                   (\(x : Tuple2 a b) (y : Tuple2 a b) ->
                                      Tuple2_match
                                        {a}
                                        {b}
                                        x
                                        {bool}
                                        (\(ipv : a) (ipv : b) ->
                                           Tuple2_match
                                             {a}
                                             {b}
                                             y
                                             {bool}
                                             (\(ipv : a) (ipv : b) ->
                                                Ordering_match
                                                  (compare {a} v ipv ipv)
                                                  {all dead. bool}
                                                  (/\dead ->
                                                     Ordering_match
                                                       (compare {b} v ipv ipv)
                                                       {all dead. bool}
                                                       (/\dead -> False)
                                                       (/\dead -> True)
                                                       (/\dead -> False)
                                                       {all dead. dead})
                                                  (/\dead -> True)
                                                  (/\dead -> False)
                                                  {all dead. dead})))
                                   (\(x : Tuple2 a b) (y : Tuple2 a b) ->
                                      Tuple2_match
                                        {a}
                                        {b}
                                        x
                                        {bool}
                                        (\(ipv : a) (ipv : b) ->
                                           Tuple2_match
                                             {a}
                                             {b}
                                             y
                                             {bool}
                                             (\(ipv : a) (ipv : b) ->
                                                Ordering_match
                                                  (compare {a} v ipv ipv)
                                                  {all dead. bool}
                                                  (/\dead ->
                                                     Ordering_match
                                                       (compare {b} v ipv ipv)
                                                       {all dead. bool}
                                                       (/\dead -> True)
                                                       (/\dead -> True)
                                                       (/\dead -> False)
                                                       {all dead. dead})
                                                  (/\dead -> True)
                                                  (/\dead -> False)
                                                  {all dead. dead})))
                                   (\(x : Tuple2 a b) (y : Tuple2 a b) ->
                                      Tuple2_match
                                        {a}
                                        {b}
                                        x
                                        {Tuple2 a b}
                                        (\(ipv : a) (ipv : b) ->
                                           Tuple2_match
                                             {a}
                                             {b}
                                             y
                                             {Tuple2 a b}
                                             (\(ipv : a) (ipv : b) ->
                                                Ordering_match
                                                  (compare {a} v ipv ipv)
                                                  {all dead. Tuple2 a b}
                                                  (/\dead ->
                                                     Ordering_match
                                                       (compare {b} v ipv ipv)
                                                       {all dead. Tuple2 a b}
                                                       (/\dead -> y)
                                                       (/\dead -> x)
                                                       (/\dead -> y)
                                                       {all dead. dead})
                                                  (/\dead -> x)
                                                  (/\dead -> y)
                                                  {all dead. dead})))
                                   (\(x : Tuple2 a b) (y : Tuple2 a b) ->
                                      Tuple2_match
                                        {a}
                                        {b}
                                        x
                                        {Tuple2 a b}
                                        (\(ipv : a) (ipv : b) ->
                                           Tuple2_match
                                             {a}
                                             {b}
                                             y
                                             {Tuple2 a b}
                                             (\(ipv : a) (ipv : b) ->
                                                Ordering_match
                                                  (compare {a} v ipv ipv)
                                                  {all dead. Tuple2 a b}
                                                  (/\dead ->
                                                     Ordering_match
                                                       (compare {b} v ipv ipv)
                                                       {all dead. Tuple2 a b}
                                                       (/\dead -> x)
                                                       (/\dead -> y)
                                                       (/\dead -> x)
                                                       {all dead. dead})
                                                  (/\dead -> y)
                                                  (/\dead -> x)
                                                  {all dead. dead}))))
                             {List integer}
                             `$dOrd`
                             `$dOrd`)
                          cp
                          x)
                   , (/\dead -> x) ]
                   {all dead. dead})
            {all dead. dead}
  in
  letrec
    !split' : Formula -> List Formula -> List Formula
      = \(ds : Formula) (a : List Formula) ->
          let
            !defaultBody : List Formula = Cons {Formula} ds a
          in
          Formula_match
            ds
            {List Formula}
            (\(p : Formula) (q : Formula) -> split' p (split' q a))
            (\(default_arg0 : Formula) (default_arg1 : Formula) -> defaultBody)
            (\(default_arg0 : Formula) (default_arg1 : Formula) -> defaultBody)
            (\(default_arg0 : Formula) (default_arg1 : Formula) -> defaultBody)
            (\(default_arg0 : Formula) -> defaultBody)
            (\(default_arg0 : integer) -> defaultBody)
  in
  let
    data StaticFormula | StaticFormula_match where
      F : StaticFormula
      F : StaticFormula
      F : StaticFormula
      F : StaticFormula
      F : StaticFormula
      F : StaticFormula
      F : StaticFormula
  in
  letrec
    !disin : Formula -> Formula
      = \(ds : Formula) ->
          Formula_match
            ds
            {Formula}
            (\(p : Formula) (q : Formula) -> Con (disin p) (disin q))
            (\(p : Formula) (ds : Formula) ->
               let
                 ~defaultBody : Formula
                   = let
                     !dq : Formula = disin ds
                     !dp : Formula = disin p
                   in
                   case
                     (all dead. Formula)
                     (case
                        (all dead. bool)
                        (Formula_match
                           dp
                           {bool}
                           (\(ds : Formula) (ds : Formula) -> True)
                           (\(default_arg0 : Formula)
                             (default_arg1 : Formula) ->
                              False)
                           (\(default_arg0 : Formula)
                             (default_arg1 : Formula) ->
                              False)
                           (\(default_arg0 : Formula)
                             (default_arg1 : Formula) ->
                              False)
                           (\(default_arg0 : Formula) -> False)
                           (\(default_arg0 : integer) -> False))
                        [ (/\dead ->
                             Formula_match
                               dq
                               {bool}
                               (\(ds : Formula) (ds : Formula) -> True)
                               (\(default_arg0 : Formula)
                                 (default_arg1 : Formula) ->
                                  False)
                               (\(default_arg0 : Formula)
                                 (default_arg1 : Formula) ->
                                  False)
                               (\(default_arg0 : Formula)
                                 (default_arg1 : Formula) ->
                                  False)
                               (\(default_arg0 : Formula) -> False)
                               (\(default_arg0 : integer) -> False))
                        , (/\dead -> True) ]
                        {all dead. dead})
                     [(/\dead -> Dis dp dq), (/\dead -> disin (Dis dp dq))]
                     {all dead. dead}
                 ~defaultBody : Formula
                   = Formula_match
                       p
                       {Formula}
                       (\(p : Formula) (q : Formula) ->
                          Con (disin (Dis p ds)) (disin (Dis q ds)))
                       (\(default_arg0 : Formula) (default_arg1 : Formula) ->
                          defaultBody)
                       (\(default_arg0 : Formula) (default_arg1 : Formula) ->
                          defaultBody)
                       (\(default_arg0 : Formula) (default_arg1 : Formula) ->
                          defaultBody)
                       (\(default_arg0 : Formula) -> defaultBody)
                       (\(default_arg0 : integer) -> defaultBody)
               in
               Formula_match
                 ds
                 {Formula}
                 (\(q : Formula) (r : Formula) ->
                    Con (disin (Dis p q)) (disin (Dis p r)))
                 (\(default_arg0 : Formula) (default_arg1 : Formula) ->
                    defaultBody)
                 (\(default_arg0 : Formula) (default_arg1 : Formula) ->
                    defaultBody)
                 (\(default_arg0 : Formula) (default_arg1 : Formula) ->
                    defaultBody)
                 (\(default_arg0 : Formula) -> defaultBody)
                 (\(default_arg0 : integer) -> defaultBody))
            (\(default_arg0 : Formula) (default_arg1 : Formula) -> ds)
            (\(default_arg0 : Formula) (default_arg1 : Formula) -> ds)
            (\(default_arg0 : Formula) -> ds)
            (\(default_arg0 : integer) -> ds)
  in
  letrec
    !elim : Formula -> Formula
      = \(ds : Formula) ->
          Formula_match
            ds
            {Formula}
            (\(p : Formula) (q : Formula) -> Con (elim p) (elim q))
            (\(p : Formula) (q : Formula) -> Dis (elim p) (elim q))
            (\(f : Formula) (f' : Formula) ->
               Con (elim (Imp f f')) (elim (Imp f' f)))
            (\(p : Formula) (q : Formula) -> Dis (Not (elim p)) (elim q))
            (\(p : Formula) -> Not (elim p))
            (\(s : integer) -> Sym s)
  in
  letrec
    !negin : Formula -> Formula
      = \(ds : Formula) ->
          Formula_match
            ds
            {Formula}
            (\(p : Formula) (q : Formula) -> Con (negin p) (negin q))
            (\(p : Formula) (q : Formula) -> Dis (negin p) (negin q))
            (\(default_arg0 : Formula) (default_arg1 : Formula) -> ds)
            (\(default_arg0 : Formula) (default_arg1 : Formula) -> ds)
            (\(ds : Formula) ->
               Formula_match
                 ds
                 {Formula}
                 (\(p : Formula) (q : Formula) ->
                    Dis (negin (Not p)) (negin (Not q)))
                 (\(p : Formula) (q : Formula) ->
                    Con (negin (Not p)) (negin (Not q)))
                 (\(default_arg0 : Formula) (default_arg1 : Formula) -> ds)
                 (\(default_arg0 : Formula) (default_arg1 : Formula) -> ds)
                 (\(p : Formula) -> negin p)
                 (\(default_arg0 : integer) -> ds))
            (\(default_arg0 : integer) -> ds)
  in
  \(eta : StaticFormula) ->
    let
      !a : List Formula
        = let
          !p : Formula
            = disin
                (negin
                   (elim
                      (StaticFormula_match
                         eta
                         {all dead. Formula}
                         (/\dead ->
                            Eqv
                              (Eqv (Sym 1) (Sym 1))
                              (Eqv (Eqv (Sym 1) (Sym 1)) (Eqv (Sym 1) (Sym 1))))
                         (/\dead ->
                            Eqv
                              (Eqv (Sym 1) (Eqv (Sym 1) (Sym 1)))
                              (Eqv (Sym 1) (Eqv (Sym 1) (Sym 1))))
                         (/\dead ->
                            Eqv
                              (Eqv (Sym 1) (Eqv (Sym 1) (Sym 1)))
                              (Eqv (Eqv (Sym 1) (Sym 1)) (Eqv (Sym 1) (Sym 1))))
                         (/\dead ->
                            Eqv
                              (Eqv (Sym 1) (Eqv (Sym 2) (Sym 3)))
                              (Eqv (Eqv (Sym 4) (Sym 5)) (Eqv (Sym 6) (Sym 7))))
                         (/\dead ->
                            Eqv
                              (Eqv (Sym 1) (Eqv (Sym 1) (Sym 1)))
                              (Eqv
                                 (Eqv (Sym 1) (Eqv (Sym 1) (Sym 1)))
                                 (Eqv (Sym 1) (Sym 1))))
                         (/\dead ->
                            Eqv
                              (Eqv (Sym 1) (Eqv (Sym 1) (Sym 1)))
                              (Eqv
                                 (Eqv (Sym 1) (Eqv (Sym 1) (Sym 1)))
                                 (Eqv (Sym 1) (Eqv (Sym 1) (Sym 1)))))
                         (/\dead ->
                            Eqv
                              (Eqv (Sym 1) (Eqv (Sym 2) (Sym 3)))
                              (Eqv
                                 (Eqv (Sym 4) (Eqv (Sym 5) (Sym 6)))
                                 (Eqv (Sym 7) (Eqv (Sym 8) (Sym 9)))))
                         {all dead. dead})))
        in
        split' p (Nil {Formula})
    in
    go a)
  (let
    data `PlutusBenchmark.NoFib.Clausify.StaticFormula` | `match_PlutusBenchmark.NoFib.Clausify.StaticFormula` where
      `PlutusBenchmark.NoFib.Clausify.F1` :
        `PlutusBenchmark.NoFib.Clausify.StaticFormula`
      `PlutusBenchmark.NoFib.Clausify.F2` :
        `PlutusBenchmark.NoFib.Clausify.StaticFormula`
      `PlutusBenchmark.NoFib.Clausify.F3` :
        `PlutusBenchmark.NoFib.Clausify.StaticFormula`
      `PlutusBenchmark.NoFib.Clausify.F4` :
        `PlutusBenchmark.NoFib.Clausify.StaticFormula`
      `PlutusBenchmark.NoFib.Clausify.F5` :
        `PlutusBenchmark.NoFib.Clausify.StaticFormula`
      `PlutusBenchmark.NoFib.Clausify.F6` :
        `PlutusBenchmark.NoFib.Clausify.StaticFormula`
      `PlutusBenchmark.NoFib.Clausify.F7` :
        `PlutusBenchmark.NoFib.Clausify.StaticFormula`
  in
  `PlutusBenchmark.NoFib.Clausify.F5`)