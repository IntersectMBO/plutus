program
  1.1.0
  (let
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
    data PredKey | PredKey_match where
      MaxValue : PredKey
      MinValue : PredKey
      NotEqual : PredKey
    data (Tuple2 :: * -> * -> *) a b | Tuple2_match where
      Tuple2 : a -> b -> Tuple2 a b
  in
  letrec
    data (List :: * -> *) a | List_match where
      Nil : List a
      Cons : a -> List a -> List a
  in
  let
    !validatePreds :
       all a. Ord a -> (\v -> List (Tuple2 PredKey (List v))) a -> a -> bool
      = /\a ->
          \(`$dOrd` : Ord a)
           (ds : (\v -> List (Tuple2 PredKey (List v))) a)
           (ds : a) ->
            letrec
              !go : List (Tuple2 PredKey (List a)) -> bool
                = \(ds : List (Tuple2 PredKey (List a))) ->
                    List_match
                      {Tuple2 PredKey (List a)}
                      ds
                      {bool}
                      True
                      (\(x : Tuple2 PredKey (List a))
                        (xs : List (Tuple2 PredKey (List a))) ->
                         Tuple2_match
                           {PredKey}
                           {List a}
                           x
                           {bool}
                           (\(predKey : PredKey)
                             (expectedPredValues : List a) ->
                              let
                                !meaning : a -> a -> bool
                                  = PredKey_match
                                      predKey
                                      {all dead. a -> a -> bool}
                                      (/\dead ->
                                         Ord_match
                                           {a}
                                           `$dOrd`
                                           {a -> a -> bool}
                                           (\(v : (\a -> a -> a -> bool) a)
                                             (v : a -> a -> Ordering)
                                             (v : a -> a -> bool)
                                             (v : a -> a -> bool)
                                             (v : a -> a -> bool)
                                             (v : a -> a -> bool)
                                             (v : a -> a -> a)
                                             (v : a -> a -> a) ->
                                              v))
                                      (/\dead ->
                                         Ord_match
                                           {a}
                                           `$dOrd`
                                           {a -> a -> bool}
                                           (\(v : (\a -> a -> a -> bool) a)
                                             (v : a -> a -> Ordering)
                                             (v : a -> a -> bool)
                                             (v : a -> a -> bool)
                                             (v : a -> a -> bool)
                                             (v : a -> a -> bool)
                                             (v : a -> a -> a)
                                             (v : a -> a -> a) ->
                                              v))
                                      (/\dead ->
                                         \(x : a) (y : a) ->
                                           case
                                             bool
                                             (Ord_match
                                                {a}
                                                `$dOrd`
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
                                                x
                                                y)
                                             [True, False])
                                      {all dead. dead}
                              in
                              letrec
                                !go : List a -> bool
                                  = \(ds : List a) ->
                                      List_match
                                        {a}
                                        ds
                                        {all dead. bool}
                                        (/\dead -> go xs)
                                        (\(x : a) (xs : List a) ->
                                           /\dead ->
                                             case
                                               (all dead. bool)
                                               (meaning x ds)
                                               [ (/\dead -> False)
                                               , (/\dead -> go xs) ]
                                               {all dead. dead})
                                        {all dead. dead}
                              in
                              go expectedPredValues))
            in
            go ds
    !`$fOrdInteger_$ccompare` : integer -> integer -> Ordering
      = \(eta : integer) (eta : integer) ->
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
            {all dead. dead}
    !ifThenElse : all a. bool -> a -> a -> a
      = /\a -> \(b : bool) (x : a) (y : a) -> case a b [y, x]
  in
  letrec
    !euclid : integer -> integer -> integer
      = \(x : integer) (y : integer) ->
          case
            (all dead. integer)
            (equalsInteger 0 y)
            [(/\dead -> euclid y (modInteger x y)), (/\dead -> x)]
            {all dead. dead}
  in
  let
    data Rational | Rational_match where
      Rational : integer -> integer -> Rational
  in
  letrec
    !unsafeRatio : integer -> integer -> Rational
      = \(n : integer) (d : integer) ->
          case
            (all dead. Rational)
            (equalsInteger 0 d)
            [ (/\dead ->
                 case
                   (all dead. Rational)
                   (lessThanInteger d 0)
                   [ (/\dead ->
                        let
                          !gcd' : integer = euclid n d
                        in
                        Rational
                          (quotientInteger n gcd')
                          (quotientInteger d gcd'))
                   , (/\dead ->
                        unsafeRatio
                          (subtractInteger 0 n)
                          (subtractInteger 0 d)) ]
                   {all dead. dead})
            , (/\dead -> error {Rational}) ]
            {all dead. dead}
  in
  letrec
    data ParamValue | ParamValue_match where
      ParamAny : ParamValue
      ParamInteger :
        (\v -> List (Tuple2 PredKey (List v))) integer -> ParamValue
      ParamList : List ParamValue -> ParamValue
      ParamRational :
        (\v -> List (Tuple2 PredKey (List v))) Rational -> ParamValue
  in
  let
    data Unit | Unit_match where
      Unit : Unit
  in
  letrec
    !validateParamValue : ParamValue -> data -> bool
      = \(eta : ParamValue) (eta : data) ->
          ParamValue_match
            eta
            {all dead. bool}
            (/\dead -> True)
            (\(preds : (\v -> List (Tuple2 PredKey (List v))) integer) ->
               /\dead ->
                 validatePreds
                   {integer}
                   (CConsOrd
                      {integer}
                      (\(x : integer) (y : integer) -> equalsInteger x y)
                      `$fOrdInteger_$ccompare`
                      (\(x : integer) (y : integer) -> lessThanInteger x y)
                      (\(x : integer) (y : integer) ->
                         lessThanEqualsInteger x y)
                      (\(x : integer) (y : integer) ->
                         ifThenElse
                           {bool}
                           (lessThanEqualsInteger x y)
                           False
                           True)
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
                           {all dead. dead}))
                   preds
                   (unIData eta))
            (\(paramValues : List ParamValue) ->
               /\dead -> validateParamValues paramValues (unListData eta))
            (\(preds : (\v -> List (Tuple2 PredKey (List v))) Rational) ->
               /\dead ->
                 validatePreds
                   {Rational}
                   (CConsOrd
                      {Rational}
                      (\(ds : Rational) (ds : Rational) ->
                         Rational_match
                           ds
                           {bool}
                           (\(n : integer) (d : integer) ->
                              Rational_match
                                ds
                                {bool}
                                (\(n' : integer) (d' : integer) ->
                                   case
                                     (all dead. bool)
                                     (equalsInteger n n')
                                     [ (/\dead -> False)
                                     , (/\dead -> equalsInteger d d') ]
                                     {all dead. dead})))
                      (\(ds : Rational) (ds : Rational) ->
                         Rational_match
                           ds
                           {Ordering}
                           (\(n : integer) (d : integer) ->
                              Rational_match
                                ds
                                {Ordering}
                                (\(n' : integer) (d' : integer) ->
                                   let
                                     !x : integer = multiplyInteger n d'
                                     !y : integer = multiplyInteger n' d
                                   in
                                   case
                                     (all dead. Ordering)
                                     (equalsInteger x y)
                                     [ (/\dead ->
                                          case
                                            (all dead. Ordering)
                                            (lessThanEqualsInteger x y)
                                            [(/\dead -> GT), (/\dead -> LT)]
                                            {all dead. dead})
                                     , (/\dead -> EQ) ]
                                     {all dead. dead})))
                      (\(ds : Rational) (ds : Rational) ->
                         Rational_match
                           ds
                           {bool}
                           (\(n : integer) (d : integer) ->
                              Rational_match
                                ds
                                {bool}
                                (\(n' : integer) (d' : integer) ->
                                   lessThanInteger
                                     (multiplyInteger n d')
                                     (multiplyInteger n' d))))
                      (\(ds : Rational) (ds : Rational) ->
                         Rational_match
                           ds
                           {bool}
                           (\(n : integer) (d : integer) ->
                              Rational_match
                                ds
                                {bool}
                                (\(n' : integer) (d' : integer) ->
                                   lessThanEqualsInteger
                                     (multiplyInteger n d')
                                     (multiplyInteger n' d))))
                      (\(ds : Rational) (ds : Rational) ->
                         Rational_match
                           ds
                           {bool}
                           (\(n : integer) (d : integer) ->
                              Rational_match
                                ds
                                {bool}
                                (\(n' : integer) (d' : integer) ->
                                   let
                                     !x : integer = multiplyInteger n d'
                                     !y : integer = multiplyInteger n' d
                                   in
                                   ifThenElse
                                     {bool}
                                     (lessThanEqualsInteger x y)
                                     False
                                     True)))
                      (\(ds : Rational) (ds : Rational) ->
                         Rational_match
                           ds
                           {bool}
                           (\(n : integer) (d : integer) ->
                              Rational_match
                                ds
                                {bool}
                                (\(n' : integer) (d' : integer) ->
                                   let
                                     !x : integer = multiplyInteger n d'
                                     !y : integer = multiplyInteger n' d
                                   in
                                   ifThenElse
                                     {bool}
                                     (lessThanInteger x y)
                                     False
                                     True)))
                      (\(x : Rational) (y : Rational) ->
                         Rational_match
                           x
                           {Rational}
                           (\(ipv : integer) (ipv : integer) ->
                              Rational_match
                                y
                                {Rational}
                                (\(ipv : integer) (ipv : integer) ->
                                   case
                                     (all dead. Rational)
                                     (lessThanEqualsInteger
                                        (multiplyInteger ipv ipv)
                                        (multiplyInteger ipv ipv))
                                     [(/\dead -> x), (/\dead -> y)]
                                     {all dead. dead})))
                      (\(x : Rational) (y : Rational) ->
                         Rational_match
                           x
                           {Rational}
                           (\(ipv : integer) (ipv : integer) ->
                              Rational_match
                                y
                                {Rational}
                                (\(ipv : integer) (ipv : integer) ->
                                   case
                                     (all dead. Rational)
                                     (lessThanEqualsInteger
                                        (multiplyInteger ipv ipv)
                                        (multiplyInteger ipv ipv))
                                     [(/\dead -> y), (/\dead -> x)]
                                     {all dead. dead}))))
                   preds
                   (let
                     !bl : list data = unListData eta
                     !bl' : list data = tailList {data} bl
                   in
                   ifThenElse
                     {Unit -> Rational}
                     (nullList {data} (tailList {data} bl'))
                     (\(ds : Unit) ->
                        unsafeRatio
                          (unIData (headList {data} bl))
                          (unIData (headList {data} bl')))
                     (\(ds : Unit) -> error {Rational})
                     Unit))
            {all dead. dead}
    !validateParamValues : List ParamValue -> list data -> bool
      = \(ds : List ParamValue) ->
          List_match
            {ParamValue}
            ds
            {list data -> bool}
            (\(eta : list data) -> nullList {data} eta)
            (\(paramValueHd : ParamValue)
              (paramValueTl : List ParamValue)
              (actualValueData : list data) ->
               case
                 (all dead. bool)
                 (validateParamValue
                    paramValueHd
                    (headList {data} actualValueData))
                 [ (/\dead -> False)
                 , (/\dead ->
                      validateParamValues
                        paramValueTl
                        (tailList {data} actualValueData)) ]
                 {all dead. dead})
  in
  letrec
    !runRules :
       List (Tuple2 integer ParamValue) -> List (Tuple2 data data) -> bool
      = \(ds : List (Tuple2 integer ParamValue))
         (cparams : List (Tuple2 data data)) ->
          let
            !fail : unit -> bool
              = \(ds : unit) ->
                  (let
                      a = Tuple2 data data
                    in
                    \(ds : List a) ->
                      List_match
                        {a}
                        ds
                        {bool}
                        True
                        (\(ipv : a) (ipv : List a) -> False))
                    cparams
          in
          List_match
            {Tuple2 integer ParamValue}
            ds
            {all dead. bool}
            (/\dead -> fail ())
            (\(ds : Tuple2 integer ParamValue)
              (cfgRest : List (Tuple2 integer ParamValue)) ->
               /\dead ->
                 Tuple2_match
                   {integer}
                   {ParamValue}
                   ds
                   {bool}
                   (\(expectedPid : integer) (paramValue : ParamValue) ->
                      List_match
                        {Tuple2 data data}
                        cparams
                        {all dead. bool}
                        (/\dead -> fail ())
                        (\(ds : Tuple2 data data)
                          (cparamsRest : List (Tuple2 data data)) ->
                           /\dead ->
                             Tuple2_match
                               {data}
                               {data}
                               ds
                               {bool}
                               (\(ds : data) (actualValueData : data) ->
                                  Ordering_match
                                    (`$fOrdInteger_$ccompare`
                                       (unIData ds)
                                       expectedPid)
                                    {all dead. bool}
                                    (/\dead ->
                                       case
                                         (all dead. bool)
                                         (validateParamValue
                                            paramValue
                                            actualValueData)
                                         [ (/\dead -> False)
                                         , (/\dead ->
                                              runRules cfgRest cparamsRest) ]
                                         {all dead. dead})
                                    (/\dead -> runRules cfgRest cparams)
                                    (/\dead -> False)
                                    {all dead. dead}))
                        {all dead. dead}))
            {all dead. dead}
  in
  let
    data (Maybe :: * -> *) a | Maybe_match where
      Just : a -> Maybe a
      Nothing : Maybe a
  in
  letrec
    ~matchData_go : list (pair data data) -> List (Tuple2 data data)
      = (let
            a = pair data data
          in
          /\r ->
            \(z : r) (f : a -> list a -> r) (xs : list a) -> case r xs [f, z])
          {List (Tuple2 data data)}
          (Nil {Tuple2 data data})
          (\(x : pair data data) (xs : list (pair data data)) ->
             Cons
               {Tuple2 data data}
               ((let
                    r = Tuple2 data data
                  in
                  \(p : pair data data) (f : data -> data -> r) -> case r p [f])
                  x
                  (\(l : data) (r : data) -> Tuple2 {data} {data} l r))
               (matchData_go xs))
  in
  let
    !fun : List (Tuple2 data data) -> bool
      = runRules
          ((let
               a = Tuple2 integer ParamValue
             in
             \(g : all b. (a -> b -> b) -> b -> b) ->
               g {List a} (\(ds : a) (ds : List a) -> Cons {a} ds ds) (Nil {a}))
             (/\a ->
                \(c : Tuple2 integer ParamValue -> a -> a) (n : a) ->
                  c
                    (Tuple2
                       {integer}
                       {ParamValue}
                       0
                       (ParamInteger
                          ((let
                               a = Tuple2 PredKey (List integer)
                             in
                             \(g : all b. (a -> b -> b) -> b -> b) ->
                               g
                                 {List a}
                                 (\(ds : a) (ds : List a) -> Cons {a} ds ds)
                                 (Nil {a}))
                             (/\a ->
                                \(c : Tuple2 PredKey (List integer) -> a -> a)
                                 (n : a) ->
                                  c
                                    (Tuple2
                                       {PredKey}
                                       {List integer}
                                       MinValue
                                       ((let
                                            a = List integer
                                          in
                                          \(c : integer -> a -> a) (n : a) ->
                                            c 30 (c 0 n))
                                          (\(ds : integer)
                                            (ds : List integer) ->
                                             Cons {integer} ds ds)
                                          (Nil {integer})))
                                    (c
                                       (Tuple2
                                          {PredKey}
                                          {List integer}
                                          MaxValue
                                          ((let
                                               a = List integer
                                             in
                                             \(c : integer -> a -> a) (n : a) ->
                                               c 1000 n)
                                             (\(ds : integer)
                                               (ds : List integer) ->
                                                Cons {integer} ds ds)
                                             (Nil {integer})))
                                       n)))))
                    (c
                       (Tuple2
                          {integer}
                          {ParamValue}
                          1
                          (ParamInteger
                             ((let
                                  a = Tuple2 PredKey (List integer)
                                in
                                \(g : all b. (a -> b -> b) -> b -> b) ->
                                  g
                                    {List a}
                                    (\(ds : a) (ds : List a) -> Cons {a} ds ds)
                                    (Nil {a}))
                                (/\a ->
                                   \(c :
                                       Tuple2 PredKey (List integer) -> a -> a)
                                    (n : a) ->
                                     c
                                       (Tuple2
                                          {PredKey}
                                          {List integer}
                                          MinValue
                                          ((let
                                               a = List integer
                                             in
                                             \(c : integer -> a -> a) (n : a) ->
                                               c 100000 (c 0 n))
                                             (\(ds : integer)
                                               (ds : List integer) ->
                                                Cons {integer} ds ds)
                                             (Nil {integer})))
                                       (c
                                          (Tuple2
                                             {PredKey}
                                             {List integer}
                                             MaxValue
                                             ((let
                                                  a = List integer
                                                in
                                                \(c : integer -> a -> a)
                                                 (n : a) ->
                                                  c 10000000 n)
                                                (\(ds : integer)
                                                  (ds : List integer) ->
                                                   Cons {integer} ds ds)
                                                (Nil {integer})))
                                          n)))))
                       (c
                          (Tuple2
                             {integer}
                             {ParamValue}
                             2
                             (ParamInteger
                                ((let
                                     a = Tuple2 PredKey (List integer)
                                   in
                                   \(g : all b. (a -> b -> b) -> b -> b) ->
                                     g
                                       {List a}
                                       (\(ds : a) (ds : List a) ->
                                          Cons {a} ds ds)
                                       (Nil {a}))
                                   (/\a ->
                                      \(c :
                                          Tuple2 PredKey (List integer) ->
                                          a ->
                                          a)
                                       (n : a) ->
                                        c
                                          (Tuple2
                                             {PredKey}
                                             {List integer}
                                             MinValue
                                             ((let
                                                  a = List integer
                                                in
                                                \(c : integer -> a -> a)
                                                 (n : a) ->
                                                  c 24576 n)
                                                (\(ds : integer)
                                                  (ds : List integer) ->
                                                   Cons {integer} ds ds)
                                                (Nil {integer})))
                                          (c
                                             (Tuple2
                                                {PredKey}
                                                {List integer}
                                                MaxValue
                                                ((let
                                                     a = List integer
                                                   in
                                                   \(c : integer -> a -> a)
                                                    (n : a) ->
                                                     c 122880 n)
                                                   (\(ds : integer)
                                                     (ds : List integer) ->
                                                      Cons {integer} ds ds)
                                                   (Nil {integer})))
                                             n)))))
                          (c
                             (Tuple2
                                {integer}
                                {ParamValue}
                                3
                                (ParamInteger
                                   ((let
                                        a = Tuple2 PredKey (List integer)
                                      in
                                      \(g : all b. (a -> b -> b) -> b -> b) ->
                                        g
                                          {List a}
                                          (\(ds : a) (ds : List a) ->
                                             Cons {a} ds ds)
                                          (Nil {a}))
                                      (/\a ->
                                         \(c :
                                             Tuple2 PredKey (List integer) ->
                                             a ->
                                             a)
                                          (n : a) ->
                                           c
                                             (Tuple2
                                                {PredKey}
                                                {List integer}
                                                MinValue
                                                ((let
                                                     a = List integer
                                                   in
                                                   \(c : integer -> a -> a)
                                                    (n : a) ->
                                                     c 0 n)
                                                   (\(ds : integer)
                                                     (ds : List integer) ->
                                                      Cons {integer} ds ds)
                                                   (Nil {integer})))
                                             (c
                                                (Tuple2
                                                   {PredKey}
                                                   {List integer}
                                                   MaxValue
                                                   ((let
                                                        a = List integer
                                                      in
                                                      \(c : integer -> a -> a)
                                                       (n : a) ->
                                                        c 32768 n)
                                                      (\(ds : integer)
                                                        (ds : List integer) ->
                                                         Cons {integer} ds ds)
                                                      (Nil {integer})))
                                                n)))))
                             (c
                                (Tuple2
                                   {integer}
                                   {ParamValue}
                                   4
                                   (ParamInteger
                                      ((let
                                           a = Tuple2 PredKey (List integer)
                                         in
                                         \(g :
                                             all b. (a -> b -> b) -> b -> b) ->
                                           g
                                             {List a}
                                             (\(ds : a) (ds : List a) ->
                                                Cons {a} ds ds)
                                             (Nil {a}))
                                         (/\a ->
                                            \(c :
                                                Tuple2 PredKey (List integer) ->
                                                a ->
                                                a)
                                             (n : a) ->
                                              c
                                                (Tuple2
                                                   {PredKey}
                                                   {List integer}
                                                   MinValue
                                                   ((let
                                                        a = List integer
                                                      in
                                                      \(c : integer -> a -> a)
                                                       (n : a) ->
                                                        c 0 n)
                                                      (\(ds : integer)
                                                        (ds : List integer) ->
                                                         Cons {integer} ds ds)
                                                      (Nil {integer})))
                                                (c
                                                   (Tuple2
                                                      {PredKey}
                                                      {List integer}
                                                      MaxValue
                                                      ((let
                                                           a = List integer
                                                         in
                                                         \(c :
                                                             integer -> a -> a)
                                                          (n : a) ->
                                                           c 5000 n)
                                                         (\(ds : integer)
                                                           (ds :
                                                              List integer) ->
                                                            Cons
                                                              {integer}
                                                              ds
                                                              ds)
                                                         (Nil {integer})))
                                                   n)))))
                                (c
                                   (Tuple2
                                      {integer}
                                      {ParamValue}
                                      5
                                      (ParamInteger
                                         ((let
                                              a = Tuple2 PredKey (List integer)
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
                                                   Tuple2
                                                     PredKey
                                                     (List integer) ->
                                                   a ->
                                                   a)
                                                (n : a) ->
                                                 c
                                                   (Tuple2
                                                      {PredKey}
                                                      {List integer}
                                                      MinValue
                                                      ((let
                                                           a = List integer
                                                         in
                                                         \(c :
                                                             integer -> a -> a)
                                                          (n : a) ->
                                                           c 1000000 (c 0 n))
                                                         (\(ds : integer)
                                                           (ds :
                                                              List integer) ->
                                                            Cons
                                                              {integer}
                                                              ds
                                                              ds)
                                                         (Nil {integer})))
                                                   (c
                                                      (Tuple2
                                                         {PredKey}
                                                         {List integer}
                                                         MaxValue
                                                         ((let
                                                              a = List integer
                                                            in
                                                            \(c :
                                                                integer ->
                                                                a ->
                                                                a)
                                                             (n : a) ->
                                                              c 5000000 n)
                                                            (\(ds : integer)
                                                              (ds :
                                                                 List
                                                                   integer) ->
                                                               Cons
                                                                 {integer}
                                                                 ds
                                                                 ds)
                                                            (Nil {integer})))
                                                      n)))))
                                   (c
                                      (Tuple2
                                         {integer}
                                         {ParamValue}
                                         6
                                         (ParamInteger
                                            ((let
                                                 a
                                                   = Tuple2
                                                       PredKey
                                                       (List integer)
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
                                                      Tuple2
                                                        PredKey
                                                        (List integer) ->
                                                      a ->
                                                      a)
                                                   (n : a) ->
                                                    c
                                                      (Tuple2
                                                         {PredKey}
                                                         {List integer}
                                                         MinValue
                                                         ((let
                                                              a = List integer
                                                            in
                                                            \(c :
                                                                integer ->
                                                                a ->
                                                                a)
                                                             (n : a) ->
                                                              c
                                                                250000000
                                                                (c 0 n))
                                                            (\(ds : integer)
                                                              (ds :
                                                                 List
                                                                   integer) ->
                                                               Cons
                                                                 {integer}
                                                                 ds
                                                                 ds)
                                                            (Nil {integer})))
                                                      (c
                                                         (Tuple2
                                                            {PredKey}
                                                            {List integer}
                                                            MaxValue
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
                                                                 c 500000000 n)
                                                               (\(ds : integer)
                                                                 (ds :
                                                                    List
                                                                      integer) ->
                                                                  Cons
                                                                    {integer}
                                                                    ds
                                                                    ds)
                                                               (Nil {integer})))
                                                         n)))))
                                      (c
                                         (Tuple2
                                            {integer}
                                            {ParamValue}
                                            7
                                            (ParamInteger
                                               ((let
                                                    a
                                                      = Tuple2
                                                          PredKey
                                                          (List integer)
                                                  in
                                                  \(g :
                                                      all b.
                                                        (a -> b -> b) ->
                                                        b ->
                                                        b) ->
                                                    g
                                                      {List a}
                                                      (\(ds : a)
                                                        (ds : List a) ->
                                                         Cons {a} ds ds)
                                                      (Nil {a}))
                                                  (/\a ->
                                                     \(c :
                                                         Tuple2
                                                           PredKey
                                                           (List integer) ->
                                                         a ->
                                                         a)
                                                      (n : a) ->
                                                       c
                                                         (Tuple2
                                                            {PredKey}
                                                            {List integer}
                                                            MinValue
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
                                                                 c 0 n)
                                                               (\(ds : integer)
                                                                 (ds :
                                                                    List
                                                                      integer) ->
                                                                  Cons
                                                                    {integer}
                                                                    ds
                                                                    ds)
                                                               (Nil {integer})))
                                                         n))))
                                         (c
                                            (Tuple2
                                               {integer}
                                               {ParamValue}
                                               8
                                               (ParamInteger
                                                  ((let
                                                       a
                                                         = Tuple2
                                                             PredKey
                                                             (List integer)
                                                     in
                                                     \(g :
                                                         all b.
                                                           (a -> b -> b) ->
                                                           b ->
                                                           b) ->
                                                       g
                                                         {List a}
                                                         (\(ds : a)
                                                           (ds : List a) ->
                                                            Cons {a} ds ds)
                                                         (Nil {a}))
                                                     (/\a ->
                                                        \(c :
                                                            Tuple2
                                                              PredKey
                                                              (List integer) ->
                                                            a ->
                                                            a)
                                                         (n : a) ->
                                                          c
                                                            (Tuple2
                                                               {PredKey}
                                                               {List integer}
                                                               MinValue
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
                                                                      250
                                                                      (c 0 n))
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
                                                                     {integer})))
                                                            (c
                                                               (Tuple2
                                                                  {PredKey}
                                                                  {List integer}
                                                                  MaxValue
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
                                                                       c 2000 n)
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
                                                                        {integer})))
                                                               (c
                                                                  (Tuple2
                                                                     {PredKey}
                                                                     {List
                                                                        integer}
                                                                     NotEqual
                                                                     ((let
                                                                          a
                                                                            = List
                                                                                integer
                                                                        in
                                                                        \(c :
                                                                            integer ->
                                                                            a ->
                                                                            a)
                                                                         (n :
                                                                            a) ->
                                                                          c 0 n)
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
                                                                           {integer})))
                                                                  n))))))
                                            (c
                                               (Tuple2
                                                  {integer}
                                                  {ParamValue}
                                                  9
                                                  (ParamRational
                                                     ((let
                                                          a
                                                            = Tuple2
                                                                PredKey
                                                                (List Rational)
                                                        in
                                                        \(g :
                                                            all b.
                                                              (a -> b -> b) ->
                                                              b ->
                                                              b) ->
                                                          g
                                                            {List a}
                                                            (\(ds : a)
                                                              (ds : List a) ->
                                                               Cons {a} ds ds)
                                                            (Nil {a}))
                                                        (/\a ->
                                                           \(c :
                                                               Tuple2
                                                                 PredKey
                                                                 (List
                                                                    Rational) ->
                                                               a ->
                                                               a)
                                                            (n : a) ->
                                                             c
                                                               (Tuple2
                                                                  {PredKey}
                                                                  {List
                                                                     Rational}
                                                                  MinValue
                                                                  ((let
                                                                       a
                                                                         = List
                                                                             Rational
                                                                     in
                                                                     \(c :
                                                                         Rational ->
                                                                         a ->
                                                                         a)
                                                                      (n : a) ->
                                                                       c
                                                                         (unsafeRatio
                                                                            1
                                                                            10)
                                                                         (c
                                                                            (unsafeRatio
                                                                               0
                                                                               1)
                                                                            n))
                                                                     (\(ds :
                                                                          Rational)
                                                                       (ds :
                                                                          List
                                                                            Rational) ->
                                                                        Cons
                                                                          {Rational}
                                                                          ds
                                                                          ds)
                                                                     (Nil
                                                                        {Rational})))
                                                               (c
                                                                  (Tuple2
                                                                     {PredKey}
                                                                     {List
                                                                        Rational}
                                                                     MaxValue
                                                                     ((let
                                                                          a
                                                                            = List
                                                                                Rational
                                                                        in
                                                                        \(c :
                                                                            Rational ->
                                                                            a ->
                                                                            a)
                                                                         (n :
                                                                            a) ->
                                                                          c
                                                                            (unsafeRatio
                                                                               1
                                                                               1)
                                                                            n)
                                                                        (\(ds :
                                                                             Rational)
                                                                          (ds :
                                                                             List
                                                                               Rational) ->
                                                                           Cons
                                                                             {Rational}
                                                                             ds
                                                                             ds)
                                                                        (Nil
                                                                           {Rational})))
                                                                  n)))))
                                               (c
                                                  (Tuple2
                                                     {integer}
                                                     {ParamValue}
                                                     10
                                                     (ParamRational
                                                        ((let
                                                             a
                                                               = Tuple2
                                                                   PredKey
                                                                   (List
                                                                      Rational)
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
                                                               (\(ds : a)
                                                                 (ds :
                                                                    List a) ->
                                                                  Cons
                                                                    {a}
                                                                    ds
                                                                    ds)
                                                               (Nil {a}))
                                                           (/\a ->
                                                              \(c :
                                                                  Tuple2
                                                                    PredKey
                                                                    (List
                                                                       Rational) ->
                                                                  a ->
                                                                  a)
                                                               (n : a) ->
                                                                c
                                                                  (Tuple2
                                                                     {PredKey}
                                                                     {List
                                                                        Rational}
                                                                     MinValue
                                                                     ((let
                                                                          a
                                                                            = List
                                                                                Rational
                                                                        in
                                                                        \(c :
                                                                            Rational ->
                                                                            a ->
                                                                            a)
                                                                         (n :
                                                                            a) ->
                                                                          c
                                                                            (unsafeRatio
                                                                               1
                                                                               1000)
                                                                            (c
                                                                               (unsafeRatio
                                                                                  0
                                                                                  1)
                                                                               n))
                                                                        (\(ds :
                                                                             Rational)
                                                                          (ds :
                                                                             List
                                                                               Rational) ->
                                                                           Cons
                                                                             {Rational}
                                                                             ds
                                                                             ds)
                                                                        (Nil
                                                                           {Rational})))
                                                                  (c
                                                                     (Tuple2
                                                                        {PredKey}
                                                                        {List
                                                                           Rational}
                                                                        MaxValue
                                                                        ((let
                                                                             a
                                                                               = List
                                                                                   Rational
                                                                           in
                                                                           \(c :
                                                                               Rational ->
                                                                               a ->
                                                                               a)
                                                                            (n :
                                                                               a) ->
                                                                             c
                                                                               (unsafeRatio
                                                                                  1
                                                                                  200)
                                                                               n)
                                                                           (\(ds :
                                                                                Rational)
                                                                             (ds :
                                                                                List
                                                                                  Rational) ->
                                                                              Cons
                                                                                {Rational}
                                                                                ds
                                                                                ds)
                                                                           (Nil
                                                                              {Rational})))
                                                                     n)))))
                                                  (c
                                                     (Tuple2
                                                        {integer}
                                                        {ParamValue}
                                                        11
                                                        (ParamRational
                                                           ((let
                                                                a
                                                                  = Tuple2
                                                                      PredKey
                                                                      (List
                                                                         Rational)
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
                                                                  (\(ds : a)
                                                                    (ds :
                                                                       List
                                                                         a) ->
                                                                     Cons
                                                                       {a}
                                                                       ds
                                                                       ds)
                                                                  (Nil {a}))
                                                              (/\a ->
                                                                 \(c :
                                                                     Tuple2
                                                                       PredKey
                                                                       (List
                                                                          Rational) ->
                                                                     a ->
                                                                     a)
                                                                  (n : a) ->
                                                                   c
                                                                     (Tuple2
                                                                        {PredKey}
                                                                        {List
                                                                           Rational}
                                                                        MinValue
                                                                        ((let
                                                                             a
                                                                               = List
                                                                                   Rational
                                                                           in
                                                                           \(c :
                                                                               Rational ->
                                                                               a ->
                                                                               a)
                                                                            (n :
                                                                               a) ->
                                                                             c
                                                                               (unsafeRatio
                                                                                  1
                                                                                  10)
                                                                               (c
                                                                                  (unsafeRatio
                                                                                     0
                                                                                     1)
                                                                                  n))
                                                                           (\(ds :
                                                                                Rational)
                                                                             (ds :
                                                                                List
                                                                                  Rational) ->
                                                                              Cons
                                                                                {Rational}
                                                                                ds
                                                                                ds)
                                                                           (Nil
                                                                              {Rational})))
                                                                     (c
                                                                        (Tuple2
                                                                           {PredKey}
                                                                           {List
                                                                              Rational}
                                                                           MaxValue
                                                                           ((let
                                                                                a
                                                                                  = List
                                                                                      Rational
                                                                              in
                                                                              \(c :
                                                                                  Rational ->
                                                                                  a ->
                                                                                  a)
                                                                               (n :
                                                                                  a) ->
                                                                                c
                                                                                  (unsafeRatio
                                                                                     3
                                                                                     10)
                                                                                  (c
                                                                                     (unsafeRatio
                                                                                        1
                                                                                        1)
                                                                                     n))
                                                                              (\(ds :
                                                                                   Rational)
                                                                                (ds :
                                                                                   List
                                                                                     Rational) ->
                                                                                 Cons
                                                                                   {Rational}
                                                                                   ds
                                                                                   ds)
                                                                              (Nil
                                                                                 {Rational})))
                                                                        n)))))
                                                     (c
                                                        (Tuple2
                                                           {integer}
                                                           {ParamValue}
                                                           16
                                                           (ParamInteger
                                                              ((let
                                                                   a
                                                                     = Tuple2
                                                                         PredKey
                                                                         (List
                                                                            integer)
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
                                                                     (\(ds : a)
                                                                       (ds :
                                                                          List
                                                                            a) ->
                                                                        Cons
                                                                          {a}
                                                                          ds
                                                                          ds)
                                                                     (Nil {a}))
                                                                 (/\a ->
                                                                    \(c :
                                                                        Tuple2
                                                                          PredKey
                                                                          (List
                                                                             integer) ->
                                                                        a ->
                                                                        a)
                                                                     (n : a) ->
                                                                      c
                                                                        (Tuple2
                                                                           {PredKey}
                                                                           {List
                                                                              integer}
                                                                           MinValue
                                                                           ((let
                                                                                a
                                                                                  = List
                                                                                      integer
                                                                              in
                                                                              \(c :
                                                                                  integer ->
                                                                                  a ->
                                                                                  a)
                                                                               (n :
                                                                                  a) ->
                                                                                c
                                                                                  0
                                                                                  n)
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
                                                                                 {integer})))
                                                                        (c
                                                                           (Tuple2
                                                                              {PredKey}
                                                                              {List
                                                                                 integer}
                                                                              MaxValue
                                                                              ((let
                                                                                   a
                                                                                     = List
                                                                                         integer
                                                                                 in
                                                                                 \(c :
                                                                                     integer ->
                                                                                     a ->
                                                                                     a)
                                                                                  (n :
                                                                                     a) ->
                                                                                   c
                                                                                     500000000
                                                                                     n)
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
                                                                                    {integer})))
                                                                           n)))))
                                                        (c
                                                           (Tuple2
                                                              {integer}
                                                              {ParamValue}
                                                              17
                                                              (ParamInteger
                                                                 ((let
                                                                      a
                                                                        = Tuple2
                                                                            PredKey
                                                                            (List
                                                                               integer)
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
                                                                             PredKey
                                                                             (List
                                                                                integer) ->
                                                                           a ->
                                                                           a)
                                                                        (n :
                                                                           a) ->
                                                                         c
                                                                           (Tuple2
                                                                              {PredKey}
                                                                              {List
                                                                                 integer}
                                                                              MinValue
                                                                              ((let
                                                                                   a
                                                                                     = List
                                                                                         integer
                                                                                 in
                                                                                 \(c :
                                                                                     integer ->
                                                                                     a ->
                                                                                     a)
                                                                                  (n :
                                                                                     a) ->
                                                                                   c
                                                                                     3000
                                                                                     (c
                                                                                        0
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
                                                                                    {integer})))
                                                                           (c
                                                                              (Tuple2
                                                                                 {PredKey}
                                                                                 {List
                                                                                    integer}
                                                                                 MaxValue
                                                                                 ((let
                                                                                      a
                                                                                        = List
                                                                                            integer
                                                                                    in
                                                                                    \(c :
                                                                                        integer ->
                                                                                        a ->
                                                                                        a)
                                                                                     (n :
                                                                                        a) ->
                                                                                      c
                                                                                        6500
                                                                                        n)
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
                                                                                       {integer})))
                                                                              (c
                                                                                 (Tuple2
                                                                                    {PredKey}
                                                                                    {List
                                                                                       integer}
                                                                                    NotEqual
                                                                                    ((let
                                                                                         a
                                                                                           = List
                                                                                               integer
                                                                                       in
                                                                                       \(c :
                                                                                           integer ->
                                                                                           a ->
                                                                                           a)
                                                                                        (n :
                                                                                           a) ->
                                                                                         c
                                                                                           0
                                                                                           n)
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
                                                                                          {integer})))
                                                                                 n))))))
                                                           (c
                                                              (Tuple2
                                                                 {integer}
                                                                 {ParamValue}
                                                                 18
                                                                 ParamAny)
                                                              (c
                                                                 (Tuple2
                                                                    {integer}
                                                                    {ParamValue}
                                                                    19
                                                                    (ParamList
                                                                       ((let
                                                                            a
                                                                              = List
                                                                                  ParamValue
                                                                          in
                                                                          \(c :
                                                                              ParamValue ->
                                                                              a ->
                                                                              a)
                                                                           (n :
                                                                              a) ->
                                                                            c
                                                                              (ParamRational
                                                                                 ((let
                                                                                      a
                                                                                        = Tuple2
                                                                                            PredKey
                                                                                            (List
                                                                                               Rational)
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
                                                                                             PredKey
                                                                                             (List
                                                                                                Rational) ->
                                                                                           a ->
                                                                                           a)
                                                                                        (n :
                                                                                           a) ->
                                                                                         c
                                                                                           (Tuple2
                                                                                              {PredKey}
                                                                                              {List
                                                                                                 Rational}
                                                                                              MinValue
                                                                                              ((let
                                                                                                   a
                                                                                                     = List
                                                                                                         Rational
                                                                                                 in
                                                                                                 \(c :
                                                                                                     Rational ->
                                                                                                     a ->
                                                                                                     a)
                                                                                                  (n :
                                                                                                     a) ->
                                                                                                   c
                                                                                                     (unsafeRatio
                                                                                                        1
                                                                                                        25)
                                                                                                     n)
                                                                                                 (\(ds :
                                                                                                      Rational)
                                                                                                   (ds :
                                                                                                      List
                                                                                                        Rational) ->
                                                                                                    Cons
                                                                                                      {Rational}
                                                                                                      ds
                                                                                                      ds)
                                                                                                 (Nil
                                                                                                    {Rational})))
                                                                                           (c
                                                                                              (Tuple2
                                                                                                 {PredKey}
                                                                                                 {List
                                                                                                    Rational}
                                                                                                 MaxValue
                                                                                                 ((let
                                                                                                      a
                                                                                                        = List
                                                                                                            Rational
                                                                                                    in
                                                                                                    \(c :
                                                                                                        Rational ->
                                                                                                        a ->
                                                                                                        a)
                                                                                                     (n :
                                                                                                        a) ->
                                                                                                      c
                                                                                                        (unsafeRatio
                                                                                                           1
                                                                                                           5)
                                                                                                        n)
                                                                                                    (\(ds :
                                                                                                         Rational)
                                                                                                      (ds :
                                                                                                         List
                                                                                                           Rational) ->
                                                                                                       Cons
                                                                                                         {Rational}
                                                                                                         ds
                                                                                                         ds)
                                                                                                    (Nil
                                                                                                       {Rational})))
                                                                                              n))))
                                                                              (c
                                                                                 (ParamRational
                                                                                    ((let
                                                                                         a
                                                                                           = Tuple2
                                                                                               PredKey
                                                                                               (List
                                                                                                  Rational)
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
                                                                                                PredKey
                                                                                                (List
                                                                                                   Rational) ->
                                                                                              a ->
                                                                                              a)
                                                                                           (n :
                                                                                              a) ->
                                                                                            c
                                                                                              (Tuple2
                                                                                                 {PredKey}
                                                                                                 {List
                                                                                                    Rational}
                                                                                                 MinValue
                                                                                                 ((let
                                                                                                      a
                                                                                                        = List
                                                                                                            Rational
                                                                                                    in
                                                                                                    \(c :
                                                                                                        Rational ->
                                                                                                        a ->
                                                                                                        a)
                                                                                                     (n :
                                                                                                        a) ->
                                                                                                      c
                                                                                                        (unsafeRatio
                                                                                                           1
                                                                                                           20000)
                                                                                                        n)
                                                                                                    (\(ds :
                                                                                                         Rational)
                                                                                                      (ds :
                                                                                                         List
                                                                                                           Rational) ->
                                                                                                       Cons
                                                                                                         {Rational}
                                                                                                         ds
                                                                                                         ds)
                                                                                                    (Nil
                                                                                                       {Rational})))
                                                                                              (c
                                                                                                 (Tuple2
                                                                                                    {PredKey}
                                                                                                    {List
                                                                                                       Rational}
                                                                                                    MaxValue
                                                                                                    ((let
                                                                                                         a
                                                                                                           = List
                                                                                                               Rational
                                                                                                       in
                                                                                                       \(c :
                                                                                                           Rational ->
                                                                                                           a ->
                                                                                                           a)
                                                                                                        (n :
                                                                                                           a) ->
                                                                                                         c
                                                                                                           (unsafeRatio
                                                                                                              1
                                                                                                              5000)
                                                                                                           n)
                                                                                                       (\(ds :
                                                                                                            Rational)
                                                                                                         (ds :
                                                                                                            List
                                                                                                              Rational) ->
                                                                                                          Cons
                                                                                                            {Rational}
                                                                                                            ds
                                                                                                            ds)
                                                                                                       (Nil
                                                                                                          {Rational})))
                                                                                                 n))))
                                                                                 n))
                                                                          (\(ds :
                                                                               ParamValue)
                                                                            (ds :
                                                                               List
                                                                                 ParamValue) ->
                                                                             Cons
                                                                               {ParamValue}
                                                                               ds
                                                                               ds)
                                                                          (Nil
                                                                             {ParamValue}))))
                                                                 (c
                                                                    (Tuple2
                                                                       {integer}
                                                                       {ParamValue}
                                                                       20
                                                                       (ParamList
                                                                          ((let
                                                                               a
                                                                                 = List
                                                                                     ParamValue
                                                                             in
                                                                             \(c :
                                                                                 ParamValue ->
                                                                                 a ->
                                                                                 a)
                                                                              (n :
                                                                                 a) ->
                                                                               c
                                                                                 (ParamInteger
                                                                                    ((let
                                                                                         a
                                                                                           = Tuple2
                                                                                               PredKey
                                                                                               (List
                                                                                                  integer)
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
                                                                                                PredKey
                                                                                                (List
                                                                                                   integer) ->
                                                                                              a ->
                                                                                              a)
                                                                                           (n :
                                                                                              a) ->
                                                                                            c
                                                                                              (Tuple2
                                                                                                 {PredKey}
                                                                                                 {List
                                                                                                    integer}
                                                                                                 MinValue
                                                                                                 ((let
                                                                                                      a
                                                                                                        = List
                                                                                                            integer
                                                                                                    in
                                                                                                    \(c :
                                                                                                        integer ->
                                                                                                        a ->
                                                                                                        a)
                                                                                                     (n :
                                                                                                        a) ->
                                                                                                      c
                                                                                                        0
                                                                                                        n)
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
                                                                                                       {integer})))
                                                                                              (c
                                                                                                 (Tuple2
                                                                                                    {PredKey}
                                                                                                    {List
                                                                                                       integer}
                                                                                                    MaxValue
                                                                                                    ((let
                                                                                                         a
                                                                                                           = List
                                                                                                               integer
                                                                                                       in
                                                                                                       \(c :
                                                                                                           integer ->
                                                                                                           a ->
                                                                                                           a)
                                                                                                        (n :
                                                                                                           a) ->
                                                                                                         c
                                                                                                           40000000
                                                                                                           n)
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
                                                                                                          {integer})))
                                                                                                 n))))
                                                                                 (c
                                                                                    (ParamInteger
                                                                                       ((let
                                                                                            a
                                                                                              = Tuple2
                                                                                                  PredKey
                                                                                                  (List
                                                                                                     integer)
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
                                                                                                   PredKey
                                                                                                   (List
                                                                                                      integer) ->
                                                                                                 a ->
                                                                                                 a)
                                                                                              (n :
                                                                                                 a) ->
                                                                                               c
                                                                                                 (Tuple2
                                                                                                    {PredKey}
                                                                                                    {List
                                                                                                       integer}
                                                                                                    MinValue
                                                                                                    ((let
                                                                                                         a
                                                                                                           = List
                                                                                                               integer
                                                                                                       in
                                                                                                       \(c :
                                                                                                           integer ->
                                                                                                           a ->
                                                                                                           a)
                                                                                                        (n :
                                                                                                           a) ->
                                                                                                         c
                                                                                                           0
                                                                                                           n)
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
                                                                                                          {integer})))
                                                                                                 (c
                                                                                                    (Tuple2
                                                                                                       {PredKey}
                                                                                                       {List
                                                                                                          integer}
                                                                                                       MaxValue
                                                                                                       ((let
                                                                                                            a
                                                                                                              = List
                                                                                                                  integer
                                                                                                          in
                                                                                                          \(c :
                                                                                                              integer ->
                                                                                                              a ->
                                                                                                              a)
                                                                                                           (n :
                                                                                                              a) ->
                                                                                                            c
                                                                                                              15000000000
                                                                                                              n)
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
                                                                                                             {integer})))
                                                                                                    n))))
                                                                                    n))
                                                                             (\(ds :
                                                                                  ParamValue)
                                                                               (ds :
                                                                                  List
                                                                                    ParamValue) ->
                                                                                Cons
                                                                                  {ParamValue}
                                                                                  ds
                                                                                  ds)
                                                                             (Nil
                                                                                {ParamValue}))))
                                                                    (c
                                                                       (Tuple2
                                                                          {integer}
                                                                          {ParamValue}
                                                                          21
                                                                          (ParamList
                                                                             ((let
                                                                                  a
                                                                                    = List
                                                                                        ParamValue
                                                                                in
                                                                                \(c :
                                                                                    ParamValue ->
                                                                                    a ->
                                                                                    a)
                                                                                 (n :
                                                                                    a) ->
                                                                                  c
                                                                                    (ParamInteger
                                                                                       ((let
                                                                                            a
                                                                                              = Tuple2
                                                                                                  PredKey
                                                                                                  (List
                                                                                                     integer)
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
                                                                                                   PredKey
                                                                                                   (List
                                                                                                      integer) ->
                                                                                                 a ->
                                                                                                 a)
                                                                                              (n :
                                                                                                 a) ->
                                                                                               c
                                                                                                 (Tuple2
                                                                                                    {PredKey}
                                                                                                    {List
                                                                                                       integer}
                                                                                                    MinValue
                                                                                                    ((let
                                                                                                         a
                                                                                                           = List
                                                                                                               integer
                                                                                                       in
                                                                                                       \(c :
                                                                                                           integer ->
                                                                                                           a ->
                                                                                                           a)
                                                                                                        (n :
                                                                                                           a) ->
                                                                                                         c
                                                                                                           0
                                                                                                           n)
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
                                                                                                          {integer})))
                                                                                                 (c
                                                                                                    (Tuple2
                                                                                                       {PredKey}
                                                                                                       {List
                                                                                                          integer}
                                                                                                       MaxValue
                                                                                                       ((let
                                                                                                            a
                                                                                                              = List
                                                                                                                  integer
                                                                                                          in
                                                                                                          \(c :
                                                                                                              integer ->
                                                                                                              a ->
                                                                                                              a)
                                                                                                           (n :
                                                                                                              a) ->
                                                                                                            c
                                                                                                              120000000
                                                                                                              n)
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
                                                                                                             {integer})))
                                                                                                    n))))
                                                                                    (c
                                                                                       (ParamInteger
                                                                                          ((let
                                                                                               a
                                                                                                 = Tuple2
                                                                                                     PredKey
                                                                                                     (List
                                                                                                        integer)
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
                                                                                                      PredKey
                                                                                                      (List
                                                                                                         integer) ->
                                                                                                    a ->
                                                                                                    a)
                                                                                                 (n :
                                                                                                    a) ->
                                                                                                  c
                                                                                                    (Tuple2
                                                                                                       {PredKey}
                                                                                                       {List
                                                                                                          integer}
                                                                                                       MinValue
                                                                                                       ((let
                                                                                                            a
                                                                                                              = List
                                                                                                                  integer
                                                                                                          in
                                                                                                          \(c :
                                                                                                              integer ->
                                                                                                              a ->
                                                                                                              a)
                                                                                                           (n :
                                                                                                              a) ->
                                                                                                            c
                                                                                                              0
                                                                                                              n)
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
                                                                                                             {integer})))
                                                                                                    (c
                                                                                                       (Tuple2
                                                                                                          {PredKey}
                                                                                                          {List
                                                                                                             integer}
                                                                                                          MaxValue
                                                                                                          ((let
                                                                                                               a
                                                                                                                 = List
                                                                                                                     integer
                                                                                                             in
                                                                                                             \(c :
                                                                                                                 integer ->
                                                                                                                 a ->
                                                                                                                 a)
                                                                                                              (n :
                                                                                                                 a) ->
                                                                                                               c
                                                                                                                 40000000000
                                                                                                                 n)
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
                                                                                                                {integer})))
                                                                                                       n))))
                                                                                       n))
                                                                                (\(ds :
                                                                                     ParamValue)
                                                                                  (ds :
                                                                                     List
                                                                                       ParamValue) ->
                                                                                   Cons
                                                                                     {ParamValue}
                                                                                     ds
                                                                                     ds)
                                                                                (Nil
                                                                                   {ParamValue}))))
                                                                       (c
                                                                          (Tuple2
                                                                             {integer}
                                                                             {ParamValue}
                                                                             22
                                                                             (ParamInteger
                                                                                ((let
                                                                                     a
                                                                                       = Tuple2
                                                                                           PredKey
                                                                                           (List
                                                                                              integer)
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
                                                                                            PredKey
                                                                                            (List
                                                                                               integer) ->
                                                                                          a ->
                                                                                          a)
                                                                                       (n :
                                                                                          a) ->
                                                                                        c
                                                                                          (Tuple2
                                                                                             {PredKey}
                                                                                             {List
                                                                                                integer}
                                                                                             MinValue
                                                                                             ((let
                                                                                                  a
                                                                                                    = List
                                                                                                        integer
                                                                                                in
                                                                                                \(c :
                                                                                                    integer ->
                                                                                                    a ->
                                                                                                    a)
                                                                                                 (n :
                                                                                                    a) ->
                                                                                                  c
                                                                                                    0
                                                                                                    n)
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
                                                                                                   {integer})))
                                                                                          (c
                                                                                             (Tuple2
                                                                                                {PredKey}
                                                                                                {List
                                                                                                   integer}
                                                                                                MaxValue
                                                                                                ((let
                                                                                                     a
                                                                                                       = List
                                                                                                           integer
                                                                                                   in
                                                                                                   \(c :
                                                                                                       integer ->
                                                                                                       a ->
                                                                                                       a)
                                                                                                    (n :
                                                                                                       a) ->
                                                                                                     c
                                                                                                       12288
                                                                                                       n)
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
                                                                                                      {integer})))
                                                                                             n)))))
                                                                          (c
                                                                             (Tuple2
                                                                                {integer}
                                                                                {ParamValue}
                                                                                23
                                                                                (ParamInteger
                                                                                   ((let
                                                                                        a
                                                                                          = Tuple2
                                                                                              PredKey
                                                                                              (List
                                                                                                 integer)
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
                                                                                               PredKey
                                                                                               (List
                                                                                                  integer) ->
                                                                                             a ->
                                                                                             a)
                                                                                          (n :
                                                                                             a) ->
                                                                                           c
                                                                                             (Tuple2
                                                                                                {PredKey}
                                                                                                {List
                                                                                                   integer}
                                                                                                MinValue
                                                                                                ((let
                                                                                                     a
                                                                                                       = List
                                                                                                           integer
                                                                                                   in
                                                                                                   \(c :
                                                                                                       integer ->
                                                                                                       a ->
                                                                                                       a)
                                                                                                    (n :
                                                                                                       a) ->
                                                                                                     c
                                                                                                       100
                                                                                                       (c
                                                                                                          0
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
                                                                                                      {integer})))
                                                                                             (c
                                                                                                (Tuple2
                                                                                                   {PredKey}
                                                                                                   {List
                                                                                                      integer}
                                                                                                   MaxValue
                                                                                                   ((let
                                                                                                        a
                                                                                                          = List
                                                                                                              integer
                                                                                                      in
                                                                                                      \(c :
                                                                                                          integer ->
                                                                                                          a ->
                                                                                                          a)
                                                                                                       (n :
                                                                                                          a) ->
                                                                                                        c
                                                                                                          200
                                                                                                          n)
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
                                                                                                         {integer})))
                                                                                                (c
                                                                                                   (Tuple2
                                                                                                      {PredKey}
                                                                                                      {List
                                                                                                         integer}
                                                                                                      NotEqual
                                                                                                      ((let
                                                                                                           a
                                                                                                             = List
                                                                                                                 integer
                                                                                                         in
                                                                                                         \(c :
                                                                                                             integer ->
                                                                                                             a ->
                                                                                                             a)
                                                                                                          (n :
                                                                                                             a) ->
                                                                                                           c
                                                                                                             0
                                                                                                             n)
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
                                                                                                            {integer})))
                                                                                                   n))))))
                                                                             (c
                                                                                (Tuple2
                                                                                   {integer}
                                                                                   {ParamValue}
                                                                                   24
                                                                                   (ParamInteger
                                                                                      ((let
                                                                                           a
                                                                                             = Tuple2
                                                                                                 PredKey
                                                                                                 (List
                                                                                                    integer)
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
                                                                                                  PredKey
                                                                                                  (List
                                                                                                     integer) ->
                                                                                                a ->
                                                                                                a)
                                                                                             (n :
                                                                                                a) ->
                                                                                              c
                                                                                                (Tuple2
                                                                                                   {PredKey}
                                                                                                   {List
                                                                                                      integer}
                                                                                                   MinValue
                                                                                                   ((let
                                                                                                        a
                                                                                                          = List
                                                                                                              integer
                                                                                                      in
                                                                                                      \(c :
                                                                                                          integer ->
                                                                                                          a ->
                                                                                                          a)
                                                                                                       (n :
                                                                                                          a) ->
                                                                                                        c
                                                                                                          1
                                                                                                          n)
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
                                                                                                         {integer})))
                                                                                                n))))
                                                                                (c
                                                                                   (Tuple2
                                                                                      {integer}
                                                                                      {ParamValue}
                                                                                      25
                                                                                      (ParamList
                                                                                         ((let
                                                                                              a
                                                                                                = List
                                                                                                    ParamValue
                                                                                            in
                                                                                            \(c :
                                                                                                ParamValue ->
                                                                                                a ->
                                                                                                a)
                                                                                             (n :
                                                                                                a) ->
                                                                                              c
                                                                                                (ParamRational
                                                                                                   ((let
                                                                                                        a
                                                                                                          = Tuple2
                                                                                                              PredKey
                                                                                                              (List
                                                                                                                 Rational)
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
                                                                                                               PredKey
                                                                                                               (List
                                                                                                                  Rational) ->
                                                                                                             a ->
                                                                                                             a)
                                                                                                          (n :
                                                                                                             a) ->
                                                                                                           c
                                                                                                             (Tuple2
                                                                                                                {PredKey}
                                                                                                                {List
                                                                                                                   Rational}
                                                                                                                MinValue
                                                                                                                ((let
                                                                                                                     a
                                                                                                                       = List
                                                                                                                           Rational
                                                                                                                   in
                                                                                                                   \(c :
                                                                                                                       Rational ->
                                                                                                                       a ->
                                                                                                                       a)
                                                                                                                    (n :
                                                                                                                       a) ->
                                                                                                                     c
                                                                                                                       (unsafeRatio
                                                                                                                          1
                                                                                                                          2)
                                                                                                                       (c
                                                                                                                          (unsafeRatio
                                                                                                                             51
                                                                                                                             100)
                                                                                                                          n))
                                                                                                                   (\(ds :
                                                                                                                        Rational)
                                                                                                                     (ds :
                                                                                                                        List
                                                                                                                          Rational) ->
                                                                                                                      Cons
                                                                                                                        {Rational}
                                                                                                                        ds
                                                                                                                        ds)
                                                                                                                   (Nil
                                                                                                                      {Rational})))
                                                                                                             (c
                                                                                                                (Tuple2
                                                                                                                   {PredKey}
                                                                                                                   {List
                                                                                                                      Rational}
                                                                                                                   MaxValue
                                                                                                                   ((let
                                                                                                                        a
                                                                                                                          = List
                                                                                                                              Rational
                                                                                                                      in
                                                                                                                      \(c :
                                                                                                                          Rational ->
                                                                                                                          a ->
                                                                                                                          a)
                                                                                                                       (n :
                                                                                                                          a) ->
                                                                                                                        c
                                                                                                                          (unsafeRatio
                                                                                                                             1
                                                                                                                             1)
                                                                                                                          (c
                                                                                                                             (unsafeRatio
                                                                                                                                3
                                                                                                                                4)
                                                                                                                             n))
                                                                                                                      (\(ds :
                                                                                                                           Rational)
                                                                                                                        (ds :
                                                                                                                           List
                                                                                                                             Rational) ->
                                                                                                                         Cons
                                                                                                                           {Rational}
                                                                                                                           ds
                                                                                                                           ds)
                                                                                                                      (Nil
                                                                                                                         {Rational})))
                                                                                                                n))))
                                                                                                (c
                                                                                                   (ParamRational
                                                                                                      ((let
                                                                                                           a
                                                                                                             = Tuple2
                                                                                                                 PredKey
                                                                                                                 (List
                                                                                                                    Rational)
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
                                                                                                                  PredKey
                                                                                                                  (List
                                                                                                                     Rational) ->
                                                                                                                a ->
                                                                                                                a)
                                                                                                             (n :
                                                                                                                a) ->
                                                                                                              c
                                                                                                                (Tuple2
                                                                                                                   {PredKey}
                                                                                                                   {List
                                                                                                                      Rational}
                                                                                                                   MinValue
                                                                                                                   ((let
                                                                                                                        a
                                                                                                                          = List
                                                                                                                              Rational
                                                                                                                      in
                                                                                                                      \(c :
                                                                                                                          Rational ->
                                                                                                                          a ->
                                                                                                                          a)
                                                                                                                       (n :
                                                                                                                          a) ->
                                                                                                                        c
                                                                                                                          (unsafeRatio
                                                                                                                             1
                                                                                                                             2)
                                                                                                                          (c
                                                                                                                             (unsafeRatio
                                                                                                                                51
                                                                                                                                100)
                                                                                                                             n))
                                                                                                                      (\(ds :
                                                                                                                           Rational)
                                                                                                                        (ds :
                                                                                                                           List
                                                                                                                             Rational) ->
                                                                                                                         Cons
                                                                                                                           {Rational}
                                                                                                                           ds
                                                                                                                           ds)
                                                                                                                      (Nil
                                                                                                                         {Rational})))
                                                                                                                (c
                                                                                                                   (Tuple2
                                                                                                                      {PredKey}
                                                                                                                      {List
                                                                                                                         Rational}
                                                                                                                      MaxValue
                                                                                                                      ((let
                                                                                                                           a
                                                                                                                             = List
                                                                                                                                 Rational
                                                                                                                         in
                                                                                                                         \(c :
                                                                                                                             Rational ->
                                                                                                                             a ->
                                                                                                                             a)
                                                                                                                          (n :
                                                                                                                             a) ->
                                                                                                                           c
                                                                                                                             (unsafeRatio
                                                                                                                                1
                                                                                                                                1)
                                                                                                                             (c
                                                                                                                                (unsafeRatio
                                                                                                                                   9
                                                                                                                                   10)
                                                                                                                                n))
                                                                                                                         (\(ds :
                                                                                                                              Rational)
                                                                                                                           (ds :
                                                                                                                              List
                                                                                                                                Rational) ->
                                                                                                                            Cons
                                                                                                                              {Rational}
                                                                                                                              ds
                                                                                                                              ds)
                                                                                                                         (Nil
                                                                                                                            {Rational})))
                                                                                                                   n))))
                                                                                                   (c
                                                                                                      (ParamRational
                                                                                                         ((let
                                                                                                              a
                                                                                                                = Tuple2
                                                                                                                    PredKey
                                                                                                                    (List
                                                                                                                       Rational)
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
                                                                                                                     PredKey
                                                                                                                     (List
                                                                                                                        Rational) ->
                                                                                                                   a ->
                                                                                                                   a)
                                                                                                                (n :
                                                                                                                   a) ->
                                                                                                                 c
                                                                                                                   (Tuple2
                                                                                                                      {PredKey}
                                                                                                                      {List
                                                                                                                         Rational}
                                                                                                                      MinValue
                                                                                                                      ((let
                                                                                                                           a
                                                                                                                             = List
                                                                                                                                 Rational
                                                                                                                         in
                                                                                                                         \(c :
                                                                                                                             Rational ->
                                                                                                                             a ->
                                                                                                                             a)
                                                                                                                          (n :
                                                                                                                             a) ->
                                                                                                                           c
                                                                                                                             (unsafeRatio
                                                                                                                                1
                                                                                                                                2)
                                                                                                                             (c
                                                                                                                                (unsafeRatio
                                                                                                                                   51
                                                                                                                                   100)
                                                                                                                                n))
                                                                                                                         (\(ds :
                                                                                                                              Rational)
                                                                                                                           (ds :
                                                                                                                              List
                                                                                                                                Rational) ->
                                                                                                                            Cons
                                                                                                                              {Rational}
                                                                                                                              ds
                                                                                                                              ds)
                                                                                                                         (Nil
                                                                                                                            {Rational})))
                                                                                                                   (c
                                                                                                                      (Tuple2
                                                                                                                         {PredKey}
                                                                                                                         {List
                                                                                                                            Rational}
                                                                                                                         MaxValue
                                                                                                                         ((let
                                                                                                                              a
                                                                                                                                = List
                                                                                                                                    Rational
                                                                                                                            in
                                                                                                                            \(c :
                                                                                                                                Rational ->
                                                                                                                                a ->
                                                                                                                                a)
                                                                                                                             (n :
                                                                                                                                a) ->
                                                                                                                              c
                                                                                                                                (unsafeRatio
                                                                                                                                   1
                                                                                                                                   1)
                                                                                                                                (c
                                                                                                                                   (unsafeRatio
                                                                                                                                      9
                                                                                                                                      10)
                                                                                                                                   n))
                                                                                                                            (\(ds :
                                                                                                                                 Rational)
                                                                                                                              (ds :
                                                                                                                                 List
                                                                                                                                   Rational) ->
                                                                                                                               Cons
                                                                                                                                 {Rational}
                                                                                                                                 ds
                                                                                                                                 ds)
                                                                                                                            (Nil
                                                                                                                               {Rational})))
                                                                                                                      n))))
                                                                                                      (c
                                                                                                         (ParamRational
                                                                                                            ((let
                                                                                                                 a
                                                                                                                   = Tuple2
                                                                                                                       PredKey
                                                                                                                       (List
                                                                                                                          Rational)
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
                                                                                                                        PredKey
                                                                                                                        (List
                                                                                                                           Rational) ->
                                                                                                                      a ->
                                                                                                                      a)
                                                                                                                   (n :
                                                                                                                      a) ->
                                                                                                                    c
                                                                                                                      (Tuple2
                                                                                                                         {PredKey}
                                                                                                                         {List
                                                                                                                            Rational}
                                                                                                                         MinValue
                                                                                                                         ((let
                                                                                                                              a
                                                                                                                                = List
                                                                                                                                    Rational
                                                                                                                            in
                                                                                                                            \(c :
                                                                                                                                Rational ->
                                                                                                                                a ->
                                                                                                                                a)
                                                                                                                             (n :
                                                                                                                                a) ->
                                                                                                                              c
                                                                                                                                (unsafeRatio
                                                                                                                                   1
                                                                                                                                   2)
                                                                                                                                (c
                                                                                                                                   (unsafeRatio
                                                                                                                                      51
                                                                                                                                      100)
                                                                                                                                   n))
                                                                                                                            (\(ds :
                                                                                                                                 Rational)
                                                                                                                              (ds :
                                                                                                                                 List
                                                                                                                                   Rational) ->
                                                                                                                               Cons
                                                                                                                                 {Rational}
                                                                                                                                 ds
                                                                                                                                 ds)
                                                                                                                            (Nil
                                                                                                                               {Rational})))
                                                                                                                      (c
                                                                                                                         (Tuple2
                                                                                                                            {PredKey}
                                                                                                                            {List
                                                                                                                               Rational}
                                                                                                                            MaxValue
                                                                                                                            ((let
                                                                                                                                 a
                                                                                                                                   = List
                                                                                                                                       Rational
                                                                                                                               in
                                                                                                                               \(c :
                                                                                                                                   Rational ->
                                                                                                                                   a ->
                                                                                                                                   a)
                                                                                                                                (n :
                                                                                                                                   a) ->
                                                                                                                                 c
                                                                                                                                   (unsafeRatio
                                                                                                                                      1
                                                                                                                                      1)
                                                                                                                                   (c
                                                                                                                                      (unsafeRatio
                                                                                                                                         4
                                                                                                                                         5)
                                                                                                                                      n))
                                                                                                                               (\(ds :
                                                                                                                                    Rational)
                                                                                                                                 (ds :
                                                                                                                                    List
                                                                                                                                      Rational) ->
                                                                                                                                  Cons
                                                                                                                                    {Rational}
                                                                                                                                    ds
                                                                                                                                    ds)
                                                                                                                               (Nil
                                                                                                                                  {Rational})))
                                                                                                                         n))))
                                                                                                         (c
                                                                                                            (ParamRational
                                                                                                               ((let
                                                                                                                    a
                                                                                                                      = Tuple2
                                                                                                                          PredKey
                                                                                                                          (List
                                                                                                                             Rational)
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
                                                                                                                           PredKey
                                                                                                                           (List
                                                                                                                              Rational) ->
                                                                                                                         a ->
                                                                                                                         a)
                                                                                                                      (n :
                                                                                                                         a) ->
                                                                                                                       c
                                                                                                                         (Tuple2
                                                                                                                            {PredKey}
                                                                                                                            {List
                                                                                                                               Rational}
                                                                                                                            MinValue
                                                                                                                            ((let
                                                                                                                                 a
                                                                                                                                   = List
                                                                                                                                       Rational
                                                                                                                               in
                                                                                                                               \(c :
                                                                                                                                   Rational ->
                                                                                                                                   a ->
                                                                                                                                   a)
                                                                                                                                (n :
                                                                                                                                   a) ->
                                                                                                                                 c
                                                                                                                                   (unsafeRatio
                                                                                                                                      1
                                                                                                                                      2)
                                                                                                                                   n)
                                                                                                                               (\(ds :
                                                                                                                                    Rational)
                                                                                                                                 (ds :
                                                                                                                                    List
                                                                                                                                      Rational) ->
                                                                                                                                  Cons
                                                                                                                                    {Rational}
                                                                                                                                    ds
                                                                                                                                    ds)
                                                                                                                               (Nil
                                                                                                                                  {Rational})))
                                                                                                                         (c
                                                                                                                            (Tuple2
                                                                                                                               {PredKey}
                                                                                                                               {List
                                                                                                                                  Rational}
                                                                                                                               MaxValue
                                                                                                                               ((let
                                                                                                                                    a
                                                                                                                                      = List
                                                                                                                                          Rational
                                                                                                                                  in
                                                                                                                                  \(c :
                                                                                                                                      Rational ->
                                                                                                                                      a ->
                                                                                                                                      a)
                                                                                                                                   (n :
                                                                                                                                      a) ->
                                                                                                                                    c
                                                                                                                                      (unsafeRatio
                                                                                                                                         1
                                                                                                                                         1)
                                                                                                                                      n)
                                                                                                                                  (\(ds :
                                                                                                                                       Rational)
                                                                                                                                    (ds :
                                                                                                                                       List
                                                                                                                                         Rational) ->
                                                                                                                                     Cons
                                                                                                                                       {Rational}
                                                                                                                                       ds
                                                                                                                                       ds)
                                                                                                                                  (Nil
                                                                                                                                     {Rational})))
                                                                                                                            n))))
                                                                                                            n)))))
                                                                                            (\(ds :
                                                                                                 ParamValue)
                                                                                              (ds :
                                                                                                 List
                                                                                                   ParamValue) ->
                                                                                               Cons
                                                                                                 {ParamValue}
                                                                                                 ds
                                                                                                 ds)
                                                                                            (Nil
                                                                                               {ParamValue}))))
                                                                                   (c
                                                                                      (Tuple2
                                                                                         {integer}
                                                                                         {ParamValue}
                                                                                         26
                                                                                         (ParamList
                                                                                            ((let
                                                                                                 a
                                                                                                   = List
                                                                                                       ParamValue
                                                                                               in
                                                                                               \(c :
                                                                                                   ParamValue ->
                                                                                                   a ->
                                                                                                   a)
                                                                                                (n :
                                                                                                   a) ->
                                                                                                 c
                                                                                                   (ParamRational
                                                                                                      ((let
                                                                                                           a
                                                                                                             = Tuple2
                                                                                                                 PredKey
                                                                                                                 (List
                                                                                                                    Rational)
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
                                                                                                                  PredKey
                                                                                                                  (List
                                                                                                                     Rational) ->
                                                                                                                a ->
                                                                                                                a)
                                                                                                             (n :
                                                                                                                a) ->
                                                                                                              c
                                                                                                                (Tuple2
                                                                                                                   {PredKey}
                                                                                                                   {List
                                                                                                                      Rational}
                                                                                                                   MinValue
                                                                                                                   ((let
                                                                                                                        a
                                                                                                                          = List
                                                                                                                              Rational
                                                                                                                      in
                                                                                                                      \(c :
                                                                                                                          Rational ->
                                                                                                                          a ->
                                                                                                                          a)
                                                                                                                       (n :
                                                                                                                          a) ->
                                                                                                                        c
                                                                                                                          (unsafeRatio
                                                                                                                             1
                                                                                                                             2)
                                                                                                                          (c
                                                                                                                             (unsafeRatio
                                                                                                                                51
                                                                                                                                100)
                                                                                                                             n))
                                                                                                                      (\(ds :
                                                                                                                           Rational)
                                                                                                                        (ds :
                                                                                                                           List
                                                                                                                             Rational) ->
                                                                                                                         Cons
                                                                                                                           {Rational}
                                                                                                                           ds
                                                                                                                           ds)
                                                                                                                      (Nil
                                                                                                                         {Rational})))
                                                                                                                (c
                                                                                                                   (Tuple2
                                                                                                                      {PredKey}
                                                                                                                      {List
                                                                                                                         Rational}
                                                                                                                      MaxValue
                                                                                                                      ((let
                                                                                                                           a
                                                                                                                             = List
                                                                                                                                 Rational
                                                                                                                         in
                                                                                                                         \(c :
                                                                                                                             Rational ->
                                                                                                                             a ->
                                                                                                                             a)
                                                                                                                          (n :
                                                                                                                             a) ->
                                                                                                                           c
                                                                                                                             (unsafeRatio
                                                                                                                                1
                                                                                                                                1)
                                                                                                                             (c
                                                                                                                                (unsafeRatio
                                                                                                                                   3
                                                                                                                                   4)
                                                                                                                                n))
                                                                                                                         (\(ds :
                                                                                                                              Rational)
                                                                                                                           (ds :
                                                                                                                              List
                                                                                                                                Rational) ->
                                                                                                                            Cons
                                                                                                                              {Rational}
                                                                                                                              ds
                                                                                                                              ds)
                                                                                                                         (Nil
                                                                                                                            {Rational})))
                                                                                                                   n))))
                                                                                                   (c
                                                                                                      (ParamRational
                                                                                                         ((let
                                                                                                              a
                                                                                                                = Tuple2
                                                                                                                    PredKey
                                                                                                                    (List
                                                                                                                       Rational)
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
                                                                                                                     PredKey
                                                                                                                     (List
                                                                                                                        Rational) ->
                                                                                                                   a ->
                                                                                                                   a)
                                                                                                                (n :
                                                                                                                   a) ->
                                                                                                                 c
                                                                                                                   (Tuple2
                                                                                                                      {PredKey}
                                                                                                                      {List
                                                                                                                         Rational}
                                                                                                                      MinValue
                                                                                                                      ((let
                                                                                                                           a
                                                                                                                             = List
                                                                                                                                 Rational
                                                                                                                         in
                                                                                                                         \(c :
                                                                                                                             Rational ->
                                                                                                                             a ->
                                                                                                                             a)
                                                                                                                          (n :
                                                                                                                             a) ->
                                                                                                                           c
                                                                                                                             (unsafeRatio
                                                                                                                                1
                                                                                                                                2)
                                                                                                                             (c
                                                                                                                                (unsafeRatio
                                                                                                                                   51
                                                                                                                                   100)
                                                                                                                                n))
                                                                                                                         (\(ds :
                                                                                                                              Rational)
                                                                                                                           (ds :
                                                                                                                              List
                                                                                                                                Rational) ->
                                                                                                                            Cons
                                                                                                                              {Rational}
                                                                                                                              ds
                                                                                                                              ds)
                                                                                                                         (Nil
                                                                                                                            {Rational})))
                                                                                                                   (c
                                                                                                                      (Tuple2
                                                                                                                         {PredKey}
                                                                                                                         {List
                                                                                                                            Rational}
                                                                                                                         MaxValue
                                                                                                                         ((let
                                                                                                                              a
                                                                                                                                = List
                                                                                                                                    Rational
                                                                                                                            in
                                                                                                                            \(c :
                                                                                                                                Rational ->
                                                                                                                                a ->
                                                                                                                                a)
                                                                                                                             (n :
                                                                                                                                a) ->
                                                                                                                              c
                                                                                                                                (unsafeRatio
                                                                                                                                   1
                                                                                                                                   1)
                                                                                                                                (c
                                                                                                                                   (unsafeRatio
                                                                                                                                      9
                                                                                                                                      10)
                                                                                                                                   n))
                                                                                                                            (\(ds :
                                                                                                                                 Rational)
                                                                                                                              (ds :
                                                                                                                                 List
                                                                                                                                   Rational) ->
                                                                                                                               Cons
                                                                                                                                 {Rational}
                                                                                                                                 ds
                                                                                                                                 ds)
                                                                                                                            (Nil
                                                                                                                               {Rational})))
                                                                                                                      n))))
                                                                                                      (c
                                                                                                         (ParamRational
                                                                                                            ((let
                                                                                                                 a
                                                                                                                   = Tuple2
                                                                                                                       PredKey
                                                                                                                       (List
                                                                                                                          Rational)
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
                                                                                                                        PredKey
                                                                                                                        (List
                                                                                                                           Rational) ->
                                                                                                                      a ->
                                                                                                                      a)
                                                                                                                   (n :
                                                                                                                      a) ->
                                                                                                                    c
                                                                                                                      (Tuple2
                                                                                                                         {PredKey}
                                                                                                                         {List
                                                                                                                            Rational}
                                                                                                                         MinValue
                                                                                                                         ((let
                                                                                                                              a
                                                                                                                                = List
                                                                                                                                    Rational
                                                                                                                            in
                                                                                                                            \(c :
                                                                                                                                Rational ->
                                                                                                                                a ->
                                                                                                                                a)
                                                                                                                             (n :
                                                                                                                                a) ->
                                                                                                                              c
                                                                                                                                (unsafeRatio
                                                                                                                                   1
                                                                                                                                   2)
                                                                                                                                (c
                                                                                                                                   (unsafeRatio
                                                                                                                                      51
                                                                                                                                      100)
                                                                                                                                   n))
                                                                                                                            (\(ds :
                                                                                                                                 Rational)
                                                                                                                              (ds :
                                                                                                                                 List
                                                                                                                                   Rational) ->
                                                                                                                               Cons
                                                                                                                                 {Rational}
                                                                                                                                 ds
                                                                                                                                 ds)
                                                                                                                            (Nil
                                                                                                                               {Rational})))
                                                                                                                      (c
                                                                                                                         (Tuple2
                                                                                                                            {PredKey}
                                                                                                                            {List
                                                                                                                               Rational}
                                                                                                                            MaxValue
                                                                                                                            ((let
                                                                                                                                 a
                                                                                                                                   = List
                                                                                                                                       Rational
                                                                                                                               in
                                                                                                                               \(c :
                                                                                                                                   Rational ->
                                                                                                                                   a ->
                                                                                                                                   a)
                                                                                                                                (n :
                                                                                                                                   a) ->
                                                                                                                                 c
                                                                                                                                   (unsafeRatio
                                                                                                                                      1
                                                                                                                                      1)
                                                                                                                                   (c
                                                                                                                                      (unsafeRatio
                                                                                                                                         9
                                                                                                                                         10)
                                                                                                                                      n))
                                                                                                                               (\(ds :
                                                                                                                                    Rational)
                                                                                                                                 (ds :
                                                                                                                                    List
                                                                                                                                      Rational) ->
                                                                                                                                  Cons
                                                                                                                                    {Rational}
                                                                                                                                    ds
                                                                                                                                    ds)
                                                                                                                               (Nil
                                                                                                                                  {Rational})))
                                                                                                                         n))))
                                                                                                         (c
                                                                                                            (ParamRational
                                                                                                               ((let
                                                                                                                    a
                                                                                                                      = Tuple2
                                                                                                                          PredKey
                                                                                                                          (List
                                                                                                                             Rational)
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
                                                                                                                           PredKey
                                                                                                                           (List
                                                                                                                              Rational) ->
                                                                                                                         a ->
                                                                                                                         a)
                                                                                                                      (n :
                                                                                                                         a) ->
                                                                                                                       c
                                                                                                                         (Tuple2
                                                                                                                            {PredKey}
                                                                                                                            {List
                                                                                                                               Rational}
                                                                                                                            MinValue
                                                                                                                            ((let
                                                                                                                                 a
                                                                                                                                   = List
                                                                                                                                       Rational
                                                                                                                               in
                                                                                                                               \(c :
                                                                                                                                   Rational ->
                                                                                                                                   a ->
                                                                                                                                   a)
                                                                                                                                (n :
                                                                                                                                   a) ->
                                                                                                                                 c
                                                                                                                                   (unsafeRatio
                                                                                                                                      1
                                                                                                                                      2)
                                                                                                                                   (c
                                                                                                                                      (unsafeRatio
                                                                                                                                         13
                                                                                                                                         20)
                                                                                                                                      n))
                                                                                                                               (\(ds :
                                                                                                                                    Rational)
                                                                                                                                 (ds :
                                                                                                                                    List
                                                                                                                                      Rational) ->
                                                                                                                                  Cons
                                                                                                                                    {Rational}
                                                                                                                                    ds
                                                                                                                                    ds)
                                                                                                                               (Nil
                                                                                                                                  {Rational})))
                                                                                                                         (c
                                                                                                                            (Tuple2
                                                                                                                               {PredKey}
                                                                                                                               {List
                                                                                                                                  Rational}
                                                                                                                               MaxValue
                                                                                                                               ((let
                                                                                                                                    a
                                                                                                                                      = List
                                                                                                                                          Rational
                                                                                                                                  in
                                                                                                                                  \(c :
                                                                                                                                      Rational ->
                                                                                                                                      a ->
                                                                                                                                      a)
                                                                                                                                   (n :
                                                                                                                                      a) ->
                                                                                                                                    c
                                                                                                                                      (unsafeRatio
                                                                                                                                         1
                                                                                                                                         1)
                                                                                                                                      (c
                                                                                                                                         (unsafeRatio
                                                                                                                                            9
                                                                                                                                            10)
                                                                                                                                         n))
                                                                                                                                  (\(ds :
                                                                                                                                       Rational)
                                                                                                                                    (ds :
                                                                                                                                       List
                                                                                                                                         Rational) ->
                                                                                                                                     Cons
                                                                                                                                       {Rational}
                                                                                                                                       ds
                                                                                                                                       ds)
                                                                                                                                  (Nil
                                                                                                                                     {Rational})))
                                                                                                                            n))))
                                                                                                            (c
                                                                                                               (ParamRational
                                                                                                                  ((let
                                                                                                                       a
                                                                                                                         = Tuple2
                                                                                                                             PredKey
                                                                                                                             (List
                                                                                                                                Rational)
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
                                                                                                                              PredKey
                                                                                                                              (List
                                                                                                                                 Rational) ->
                                                                                                                            a ->
                                                                                                                            a)
                                                                                                                         (n :
                                                                                                                            a) ->
                                                                                                                          c
                                                                                                                            (Tuple2
                                                                                                                               {PredKey}
                                                                                                                               {List
                                                                                                                                  Rational}
                                                                                                                               MinValue
                                                                                                                               ((let
                                                                                                                                    a
                                                                                                                                      = List
                                                                                                                                          Rational
                                                                                                                                  in
                                                                                                                                  \(c :
                                                                                                                                      Rational ->
                                                                                                                                      a ->
                                                                                                                                      a)
                                                                                                                                   (n :
                                                                                                                                      a) ->
                                                                                                                                    c
                                                                                                                                      (unsafeRatio
                                                                                                                                         1
                                                                                                                                         2)
                                                                                                                                      (c
                                                                                                                                         (unsafeRatio
                                                                                                                                            51
                                                                                                                                            100)
                                                                                                                                         n))
                                                                                                                                  (\(ds :
                                                                                                                                       Rational)
                                                                                                                                    (ds :
                                                                                                                                       List
                                                                                                                                         Rational) ->
                                                                                                                                     Cons
                                                                                                                                       {Rational}
                                                                                                                                       ds
                                                                                                                                       ds)
                                                                                                                                  (Nil
                                                                                                                                     {Rational})))
                                                                                                                            (c
                                                                                                                               (Tuple2
                                                                                                                                  {PredKey}
                                                                                                                                  {List
                                                                                                                                     Rational}
                                                                                                                                  MaxValue
                                                                                                                                  ((let
                                                                                                                                       a
                                                                                                                                         = List
                                                                                                                                             Rational
                                                                                                                                     in
                                                                                                                                     \(c :
                                                                                                                                         Rational ->
                                                                                                                                         a ->
                                                                                                                                         a)
                                                                                                                                      (n :
                                                                                                                                         a) ->
                                                                                                                                       c
                                                                                                                                         (unsafeRatio
                                                                                                                                            1
                                                                                                                                            1)
                                                                                                                                         (c
                                                                                                                                            (unsafeRatio
                                                                                                                                               4
                                                                                                                                               5)
                                                                                                                                            n))
                                                                                                                                     (\(ds :
                                                                                                                                          Rational)
                                                                                                                                       (ds :
                                                                                                                                          List
                                                                                                                                            Rational) ->
                                                                                                                                        Cons
                                                                                                                                          {Rational}
                                                                                                                                          ds
                                                                                                                                          ds)
                                                                                                                                     (Nil
                                                                                                                                        {Rational})))
                                                                                                                               n))))
                                                                                                               (c
                                                                                                                  (ParamRational
                                                                                                                     ((let
                                                                                                                          a
                                                                                                                            = Tuple2
                                                                                                                                PredKey
                                                                                                                                (List
                                                                                                                                   Rational)
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
                                                                                                                                 PredKey
                                                                                                                                 (List
                                                                                                                                    Rational) ->
                                                                                                                               a ->
                                                                                                                               a)
                                                                                                                            (n :
                                                                                                                               a) ->
                                                                                                                             c
                                                                                                                               (Tuple2
                                                                                                                                  {PredKey}
                                                                                                                                  {List
                                                                                                                                     Rational}
                                                                                                                                  MinValue
                                                                                                                                  ((let
                                                                                                                                       a
                                                                                                                                         = List
                                                                                                                                             Rational
                                                                                                                                     in
                                                                                                                                     \(c :
                                                                                                                                         Rational ->
                                                                                                                                         a ->
                                                                                                                                         a)
                                                                                                                                      (n :
                                                                                                                                         a) ->
                                                                                                                                       c
                                                                                                                                         (unsafeRatio
                                                                                                                                            1
                                                                                                                                            2)
                                                                                                                                         (c
                                                                                                                                            (unsafeRatio
                                                                                                                                               51
                                                                                                                                               100)
                                                                                                                                            n))
                                                                                                                                     (\(ds :
                                                                                                                                          Rational)
                                                                                                                                       (ds :
                                                                                                                                          List
                                                                                                                                            Rational) ->
                                                                                                                                        Cons
                                                                                                                                          {Rational}
                                                                                                                                          ds
                                                                                                                                          ds)
                                                                                                                                     (Nil
                                                                                                                                        {Rational})))
                                                                                                                               (c
                                                                                                                                  (Tuple2
                                                                                                                                     {PredKey}
                                                                                                                                     {List
                                                                                                                                        Rational}
                                                                                                                                     MaxValue
                                                                                                                                     ((let
                                                                                                                                          a
                                                                                                                                            = List
                                                                                                                                                Rational
                                                                                                                                        in
                                                                                                                                        \(c :
                                                                                                                                            Rational ->
                                                                                                                                            a ->
                                                                                                                                            a)
                                                                                                                                         (n :
                                                                                                                                            a) ->
                                                                                                                                          c
                                                                                                                                            (unsafeRatio
                                                                                                                                               1
                                                                                                                                               1)
                                                                                                                                            (c
                                                                                                                                               (unsafeRatio
                                                                                                                                                  3
                                                                                                                                                  4)
                                                                                                                                               n))
                                                                                                                                        (\(ds :
                                                                                                                                             Rational)
                                                                                                                                          (ds :
                                                                                                                                             List
                                                                                                                                               Rational) ->
                                                                                                                                           Cons
                                                                                                                                             {Rational}
                                                                                                                                             ds
                                                                                                                                             ds)
                                                                                                                                        (Nil
                                                                                                                                           {Rational})))
                                                                                                                                  n))))
                                                                                                                  (c
                                                                                                                     (ParamRational
                                                                                                                        ((let
                                                                                                                             a
                                                                                                                               = Tuple2
                                                                                                                                   PredKey
                                                                                                                                   (List
                                                                                                                                      Rational)
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
                                                                                                                                    PredKey
                                                                                                                                    (List
                                                                                                                                       Rational) ->
                                                                                                                                  a ->
                                                                                                                                  a)
                                                                                                                               (n :
                                                                                                                                  a) ->
                                                                                                                                c
                                                                                                                                  (Tuple2
                                                                                                                                     {PredKey}
                                                                                                                                     {List
                                                                                                                                        Rational}
                                                                                                                                     MinValue
                                                                                                                                     ((let
                                                                                                                                          a
                                                                                                                                            = List
                                                                                                                                                Rational
                                                                                                                                        in
                                                                                                                                        \(c :
                                                                                                                                            Rational ->
                                                                                                                                            a ->
                                                                                                                                            a)
                                                                                                                                         (n :
                                                                                                                                            a) ->
                                                                                                                                          c
                                                                                                                                            (unsafeRatio
                                                                                                                                               1
                                                                                                                                               2)
                                                                                                                                            (c
                                                                                                                                               (unsafeRatio
                                                                                                                                                  51
                                                                                                                                                  100)
                                                                                                                                               n))
                                                                                                                                        (\(ds :
                                                                                                                                             Rational)
                                                                                                                                          (ds :
                                                                                                                                             List
                                                                                                                                               Rational) ->
                                                                                                                                           Cons
                                                                                                                                             {Rational}
                                                                                                                                             ds
                                                                                                                                             ds)
                                                                                                                                        (Nil
                                                                                                                                           {Rational})))
                                                                                                                                  (c
                                                                                                                                     (Tuple2
                                                                                                                                        {PredKey}
                                                                                                                                        {List
                                                                                                                                           Rational}
                                                                                                                                        MaxValue
                                                                                                                                        ((let
                                                                                                                                             a
                                                                                                                                               = List
                                                                                                                                                   Rational
                                                                                                                                           in
                                                                                                                                           \(c :
                                                                                                                                               Rational ->
                                                                                                                                               a ->
                                                                                                                                               a)
                                                                                                                                            (n :
                                                                                                                                               a) ->
                                                                                                                                             c
                                                                                                                                               (unsafeRatio
                                                                                                                                                  1
                                                                                                                                                  1)
                                                                                                                                               (c
                                                                                                                                                  (unsafeRatio
                                                                                                                                                     3
                                                                                                                                                     4)
                                                                                                                                                  n))
                                                                                                                                           (\(ds :
                                                                                                                                                Rational)
                                                                                                                                             (ds :
                                                                                                                                                List
                                                                                                                                                  Rational) ->
                                                                                                                                              Cons
                                                                                                                                                {Rational}
                                                                                                                                                ds
                                                                                                                                                ds)
                                                                                                                                           (Nil
                                                                                                                                              {Rational})))
                                                                                                                                     n))))
                                                                                                                     (c
                                                                                                                        (ParamRational
                                                                                                                           ((let
                                                                                                                                a
                                                                                                                                  = Tuple2
                                                                                                                                      PredKey
                                                                                                                                      (List
                                                                                                                                         Rational)
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
                                                                                                                                       PredKey
                                                                                                                                       (List
                                                                                                                                          Rational) ->
                                                                                                                                     a ->
                                                                                                                                     a)
                                                                                                                                  (n :
                                                                                                                                     a) ->
                                                                                                                                   c
                                                                                                                                     (Tuple2
                                                                                                                                        {PredKey}
                                                                                                                                        {List
                                                                                                                                           Rational}
                                                                                                                                        MinValue
                                                                                                                                        ((let
                                                                                                                                             a
                                                                                                                                               = List
                                                                                                                                                   Rational
                                                                                                                                           in
                                                                                                                                           \(c :
                                                                                                                                               Rational ->
                                                                                                                                               a ->
                                                                                                                                               a)
                                                                                                                                            (n :
                                                                                                                                               a) ->
                                                                                                                                             c
                                                                                                                                               (unsafeRatio
                                                                                                                                                  1
                                                                                                                                                  2)
                                                                                                                                               (c
                                                                                                                                                  (unsafeRatio
                                                                                                                                                     51
                                                                                                                                                     100)
                                                                                                                                                  n))
                                                                                                                                           (\(ds :
                                                                                                                                                Rational)
                                                                                                                                             (ds :
                                                                                                                                                List
                                                                                                                                                  Rational) ->
                                                                                                                                              Cons
                                                                                                                                                {Rational}
                                                                                                                                                ds
                                                                                                                                                ds)
                                                                                                                                           (Nil
                                                                                                                                              {Rational})))
                                                                                                                                     (c
                                                                                                                                        (Tuple2
                                                                                                                                           {PredKey}
                                                                                                                                           {List
                                                                                                                                              Rational}
                                                                                                                                           MaxValue
                                                                                                                                           ((let
                                                                                                                                                a
                                                                                                                                                  = List
                                                                                                                                                      Rational
                                                                                                                                              in
                                                                                                                                              \(c :
                                                                                                                                                  Rational ->
                                                                                                                                                  a ->
                                                                                                                                                  a)
                                                                                                                                               (n :
                                                                                                                                                  a) ->
                                                                                                                                                c
                                                                                                                                                  (unsafeRatio
                                                                                                                                                     1
                                                                                                                                                     1)
                                                                                                                                                  (c
                                                                                                                                                     (unsafeRatio
                                                                                                                                                        3
                                                                                                                                                        4)
                                                                                                                                                     n))
                                                                                                                                              (\(ds :
                                                                                                                                                   Rational)
                                                                                                                                                (ds :
                                                                                                                                                   List
                                                                                                                                                     Rational) ->
                                                                                                                                                 Cons
                                                                                                                                                   {Rational}
                                                                                                                                                   ds
                                                                                                                                                   ds)
                                                                                                                                              (Nil
                                                                                                                                                 {Rational})))
                                                                                                                                        n))))
                                                                                                                        (c
                                                                                                                           (ParamRational
                                                                                                                              ((let
                                                                                                                                   a
                                                                                                                                     = Tuple2
                                                                                                                                         PredKey
                                                                                                                                         (List
                                                                                                                                            Rational)
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
                                                                                                                                          PredKey
                                                                                                                                          (List
                                                                                                                                             Rational) ->
                                                                                                                                        a ->
                                                                                                                                        a)
                                                                                                                                     (n :
                                                                                                                                        a) ->
                                                                                                                                      c
                                                                                                                                        (Tuple2
                                                                                                                                           {PredKey}
                                                                                                                                           {List
                                                                                                                                              Rational}
                                                                                                                                           MinValue
                                                                                                                                           ((let
                                                                                                                                                a
                                                                                                                                                  = List
                                                                                                                                                      Rational
                                                                                                                                              in
                                                                                                                                              \(c :
                                                                                                                                                  Rational ->
                                                                                                                                                  a ->
                                                                                                                                                  a)
                                                                                                                                               (n :
                                                                                                                                                  a) ->
                                                                                                                                                c
                                                                                                                                                  (unsafeRatio
                                                                                                                                                     1
                                                                                                                                                     2)
                                                                                                                                                  (c
                                                                                                                                                     (unsafeRatio
                                                                                                                                                        3
                                                                                                                                                        4)
                                                                                                                                                     n))
                                                                                                                                              (\(ds :
                                                                                                                                                   Rational)
                                                                                                                                                (ds :
                                                                                                                                                   List
                                                                                                                                                     Rational) ->
                                                                                                                                                 Cons
                                                                                                                                                   {Rational}
                                                                                                                                                   ds
                                                                                                                                                   ds)
                                                                                                                                              (Nil
                                                                                                                                                 {Rational})))
                                                                                                                                        (c
                                                                                                                                           (Tuple2
                                                                                                                                              {PredKey}
                                                                                                                                              {List
                                                                                                                                                 Rational}
                                                                                                                                              MaxValue
                                                                                                                                              ((let
                                                                                                                                                   a
                                                                                                                                                     = List
                                                                                                                                                         Rational
                                                                                                                                                 in
                                                                                                                                                 \(c :
                                                                                                                                                     Rational ->
                                                                                                                                                     a ->
                                                                                                                                                     a)
                                                                                                                                                  (n :
                                                                                                                                                     a) ->
                                                                                                                                                   c
                                                                                                                                                     (unsafeRatio
                                                                                                                                                        1
                                                                                                                                                        1)
                                                                                                                                                     (c
                                                                                                                                                        (unsafeRatio
                                                                                                                                                           9
                                                                                                                                                           10)
                                                                                                                                                        n))
                                                                                                                                                 (\(ds :
                                                                                                                                                      Rational)
                                                                                                                                                   (ds :
                                                                                                                                                      List
                                                                                                                                                        Rational) ->
                                                                                                                                                    Cons
                                                                                                                                                      {Rational}
                                                                                                                                                      ds
                                                                                                                                                      ds)
                                                                                                                                                 (Nil
                                                                                                                                                    {Rational})))
                                                                                                                                           n))))
                                                                                                                           (c
                                                                                                                              (ParamRational
                                                                                                                                 ((let
                                                                                                                                      a
                                                                                                                                        = Tuple2
                                                                                                                                            PredKey
                                                                                                                                            (List
                                                                                                                                               Rational)
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
                                                                                                                                             PredKey
                                                                                                                                             (List
                                                                                                                                                Rational) ->
                                                                                                                                           a ->
                                                                                                                                           a)
                                                                                                                                        (n :
                                                                                                                                           a) ->
                                                                                                                                         c
                                                                                                                                           (Tuple2
                                                                                                                                              {PredKey}
                                                                                                                                              {List
                                                                                                                                                 Rational}
                                                                                                                                              MinValue
                                                                                                                                              ((let
                                                                                                                                                   a
                                                                                                                                                     = List
                                                                                                                                                         Rational
                                                                                                                                                 in
                                                                                                                                                 \(c :
                                                                                                                                                     Rational ->
                                                                                                                                                     a ->
                                                                                                                                                     a)
                                                                                                                                                  (n :
                                                                                                                                                     a) ->
                                                                                                                                                   c
                                                                                                                                                     (unsafeRatio
                                                                                                                                                        1
                                                                                                                                                        2)
                                                                                                                                                     n)
                                                                                                                                                 (\(ds :
                                                                                                                                                      Rational)
                                                                                                                                                   (ds :
                                                                                                                                                      List
                                                                                                                                                        Rational) ->
                                                                                                                                                    Cons
                                                                                                                                                      {Rational}
                                                                                                                                                      ds
                                                                                                                                                      ds)
                                                                                                                                                 (Nil
                                                                                                                                                    {Rational})))
                                                                                                                                           (c
                                                                                                                                              (Tuple2
                                                                                                                                                 {PredKey}
                                                                                                                                                 {List
                                                                                                                                                    Rational}
                                                                                                                                                 MaxValue
                                                                                                                                                 ((let
                                                                                                                                                      a
                                                                                                                                                        = List
                                                                                                                                                            Rational
                                                                                                                                                    in
                                                                                                                                                    \(c :
                                                                                                                                                        Rational ->
                                                                                                                                                        a ->
                                                                                                                                                        a)
                                                                                                                                                     (n :
                                                                                                                                                        a) ->
                                                                                                                                                      c
                                                                                                                                                        (unsafeRatio
                                                                                                                                                           1
                                                                                                                                                           1)
                                                                                                                                                        n)
                                                                                                                                                    (\(ds :
                                                                                                                                                         Rational)
                                                                                                                                                      (ds :
                                                                                                                                                         List
                                                                                                                                                           Rational) ->
                                                                                                                                                       Cons
                                                                                                                                                         {Rational}
                                                                                                                                                         ds
                                                                                                                                                         ds)
                                                                                                                                                    (Nil
                                                                                                                                                       {Rational})))
                                                                                                                                              n))))
                                                                                                                              n))))))))))
                                                                                               (\(ds :
                                                                                                    ParamValue)
                                                                                                 (ds :
                                                                                                    List
                                                                                                      ParamValue) ->
                                                                                                  Cons
                                                                                                    {ParamValue}
                                                                                                    ds
                                                                                                    ds)
                                                                                               (Nil
                                                                                                  {ParamValue}))))
                                                                                      (c
                                                                                         (Tuple2
                                                                                            {integer}
                                                                                            {ParamValue}
                                                                                            27
                                                                                            (ParamInteger
                                                                                               ((let
                                                                                                    a
                                                                                                      = Tuple2
                                                                                                          PredKey
                                                                                                          (List
                                                                                                             integer)
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
                                                                                                           PredKey
                                                                                                           (List
                                                                                                              integer) ->
                                                                                                         a ->
                                                                                                         a)
                                                                                                      (n :
                                                                                                         a) ->
                                                                                                       c
                                                                                                         (Tuple2
                                                                                                            {PredKey}
                                                                                                            {List
                                                                                                               integer}
                                                                                                            MinValue
                                                                                                            ((let
                                                                                                                 a
                                                                                                                   = List
                                                                                                                       integer
                                                                                                               in
                                                                                                               \(c :
                                                                                                                   integer ->
                                                                                                                   a ->
                                                                                                                   a)
                                                                                                                (n :
                                                                                                                   a) ->
                                                                                                                 c
                                                                                                                   0
                                                                                                                   (c
                                                                                                                      3
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
                                                                                                                  {integer})))
                                                                                                         (c
                                                                                                            (Tuple2
                                                                                                               {PredKey}
                                                                                                               {List
                                                                                                                  integer}
                                                                                                               MaxValue
                                                                                                               ((let
                                                                                                                    a
                                                                                                                      = List
                                                                                                                          integer
                                                                                                                  in
                                                                                                                  \(c :
                                                                                                                      integer ->
                                                                                                                      a ->
                                                                                                                      a)
                                                                                                                   (n :
                                                                                                                      a) ->
                                                                                                                    c
                                                                                                                      10
                                                                                                                      n)
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
                                                                                                                     {integer})))
                                                                                                            n)))))
                                                                                         (c
                                                                                            (Tuple2
                                                                                               {integer}
                                                                                               {ParamValue}
                                                                                               28
                                                                                               (ParamInteger
                                                                                                  ((let
                                                                                                       a
                                                                                                         = Tuple2
                                                                                                             PredKey
                                                                                                             (List
                                                                                                                integer)
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
                                                                                                              PredKey
                                                                                                              (List
                                                                                                                 integer) ->
                                                                                                            a ->
                                                                                                            a)
                                                                                                         (n :
                                                                                                            a) ->
                                                                                                          c
                                                                                                            (Tuple2
                                                                                                               {PredKey}
                                                                                                               {List
                                                                                                                  integer}
                                                                                                               MinValue
                                                                                                               ((let
                                                                                                                    a
                                                                                                                      = List
                                                                                                                          integer
                                                                                                                  in
                                                                                                                  \(c :
                                                                                                                      integer ->
                                                                                                                      a ->
                                                                                                                      a)
                                                                                                                   (n :
                                                                                                                      a) ->
                                                                                                                    c
                                                                                                                      0
                                                                                                                      (c
                                                                                                                         18
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
                                                                                                                     {integer})))
                                                                                                            (c
                                                                                                               (Tuple2
                                                                                                                  {PredKey}
                                                                                                                  {List
                                                                                                                     integer}
                                                                                                                  MaxValue
                                                                                                                  ((let
                                                                                                                       a
                                                                                                                         = List
                                                                                                                             integer
                                                                                                                     in
                                                                                                                     \(c :
                                                                                                                         integer ->
                                                                                                                         a ->
                                                                                                                         a)
                                                                                                                      (n :
                                                                                                                         a) ->
                                                                                                                       c
                                                                                                                         293
                                                                                                                         n)
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
                                                                                                                        {integer})))
                                                                                                               (c
                                                                                                                  (Tuple2
                                                                                                                     {PredKey}
                                                                                                                     {List
                                                                                                                        integer}
                                                                                                                     NotEqual
                                                                                                                     ((let
                                                                                                                          a
                                                                                                                            = List
                                                                                                                                integer
                                                                                                                        in
                                                                                                                        \(c :
                                                                                                                            integer ->
                                                                                                                            a ->
                                                                                                                            a)
                                                                                                                         (n :
                                                                                                                            a) ->
                                                                                                                          c
                                                                                                                            0
                                                                                                                            n)
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
                                                                                                                           {integer})))
                                                                                                                  n))))))
                                                                                            (c
                                                                                               (Tuple2
                                                                                                  {integer}
                                                                                                  {ParamValue}
                                                                                                  29
                                                                                                  (ParamInteger
                                                                                                     ((let
                                                                                                          a
                                                                                                            = Tuple2
                                                                                                                PredKey
                                                                                                                (List
                                                                                                                   integer)
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
                                                                                                                 PredKey
                                                                                                                 (List
                                                                                                                    integer) ->
                                                                                                               a ->
                                                                                                               a)
                                                                                                            (n :
                                                                                                               a) ->
                                                                                                             c
                                                                                                               (Tuple2
                                                                                                                  {PredKey}
                                                                                                                  {List
                                                                                                                     integer}
                                                                                                                  MinValue
                                                                                                                  ((let
                                                                                                                       a
                                                                                                                         = List
                                                                                                                             integer
                                                                                                                     in
                                                                                                                     \(c :
                                                                                                                         integer ->
                                                                                                                         a ->
                                                                                                                         a)
                                                                                                                      (n :
                                                                                                                         a) ->
                                                                                                                       c
                                                                                                                         1
                                                                                                                         n)
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
                                                                                                                        {integer})))
                                                                                                               (c
                                                                                                                  (Tuple2
                                                                                                                     {PredKey}
                                                                                                                     {List
                                                                                                                        integer}
                                                                                                                     MaxValue
                                                                                                                     ((let
                                                                                                                          a
                                                                                                                            = List
                                                                                                                                integer
                                                                                                                        in
                                                                                                                        \(c :
                                                                                                                            integer ->
                                                                                                                            a ->
                                                                                                                            a)
                                                                                                                         (n :
                                                                                                                            a) ->
                                                                                                                          c
                                                                                                                            15
                                                                                                                            n)
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
                                                                                                                           {integer})))
                                                                                                                  n)))))
                                                                                               (c
                                                                                                  (Tuple2
                                                                                                     {integer}
                                                                                                     {ParamValue}
                                                                                                     30
                                                                                                     (ParamInteger
                                                                                                        ((let
                                                                                                             a
                                                                                                               = Tuple2
                                                                                                                   PredKey
                                                                                                                   (List
                                                                                                                      integer)
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
                                                                                                                    PredKey
                                                                                                                    (List
                                                                                                                       integer) ->
                                                                                                                  a ->
                                                                                                                  a)
                                                                                                               (n :
                                                                                                                  a) ->
                                                                                                                c
                                                                                                                  (Tuple2
                                                                                                                     {PredKey}
                                                                                                                     {List
                                                                                                                        integer}
                                                                                                                     MinValue
                                                                                                                     ((let
                                                                                                                          a
                                                                                                                            = List
                                                                                                                                integer
                                                                                                                        in
                                                                                                                        \(c :
                                                                                                                            integer ->
                                                                                                                            a ->
                                                                                                                            a)
                                                                                                                         (n :
                                                                                                                            a) ->
                                                                                                                          c
                                                                                                                            0
                                                                                                                            (c
                                                                                                                               1000000
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
                                                                                                                           {integer})))
                                                                                                                  (c
                                                                                                                     (Tuple2
                                                                                                                        {PredKey}
                                                                                                                        {List
                                                                                                                           integer}
                                                                                                                        MaxValue
                                                                                                                        ((let
                                                                                                                             a
                                                                                                                               = List
                                                                                                                                   integer
                                                                                                                           in
                                                                                                                           \(c :
                                                                                                                               integer ->
                                                                                                                               a ->
                                                                                                                               a)
                                                                                                                            (n :
                                                                                                                               a) ->
                                                                                                                             c
                                                                                                                               10000000000000
                                                                                                                               n)
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
                                                                                                                              {integer})))
                                                                                                                     n)))))
                                                                                                  (c
                                                                                                     (Tuple2
                                                                                                        {integer}
                                                                                                        {ParamValue}
                                                                                                        31
                                                                                                        (ParamInteger
                                                                                                           ((let
                                                                                                                a
                                                                                                                  = Tuple2
                                                                                                                      PredKey
                                                                                                                      (List
                                                                                                                         integer)
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
                                                                                                                       PredKey
                                                                                                                       (List
                                                                                                                          integer) ->
                                                                                                                     a ->
                                                                                                                     a)
                                                                                                                  (n :
                                                                                                                     a) ->
                                                                                                                   c
                                                                                                                     (Tuple2
                                                                                                                        {PredKey}
                                                                                                                        {List
                                                                                                                           integer}
                                                                                                                        MinValue
                                                                                                                        ((let
                                                                                                                             a
                                                                                                                               = List
                                                                                                                                   integer
                                                                                                                           in
                                                                                                                           \(c :
                                                                                                                               integer ->
                                                                                                                               a ->
                                                                                                                               a)
                                                                                                                            (n :
                                                                                                                               a) ->
                                                                                                                             c
                                                                                                                               0
                                                                                                                               (c
                                                                                                                                  1000000
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
                                                                                                                              {integer})))
                                                                                                                     (c
                                                                                                                        (Tuple2
                                                                                                                           {PredKey}
                                                                                                                           {List
                                                                                                                              integer}
                                                                                                                           MaxValue
                                                                                                                           ((let
                                                                                                                                a
                                                                                                                                  = List
                                                                                                                                      integer
                                                                                                                              in
                                                                                                                              \(c :
                                                                                                                                  integer ->
                                                                                                                                  a ->
                                                                                                                                  a)
                                                                                                                               (n :
                                                                                                                                  a) ->
                                                                                                                                c
                                                                                                                                  100000000000
                                                                                                                                  n)
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
                                                                                                                                 {integer})))
                                                                                                                        n)))))
                                                                                                     (c
                                                                                                        (Tuple2
                                                                                                           {integer}
                                                                                                           {ParamValue}
                                                                                                           32
                                                                                                           (ParamInteger
                                                                                                              ((let
                                                                                                                   a
                                                                                                                     = Tuple2
                                                                                                                         PredKey
                                                                                                                         (List
                                                                                                                            integer)
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
                                                                                                                          PredKey
                                                                                                                          (List
                                                                                                                             integer) ->
                                                                                                                        a ->
                                                                                                                        a)
                                                                                                                     (n :
                                                                                                                        a) ->
                                                                                                                      c
                                                                                                                        (Tuple2
                                                                                                                           {PredKey}
                                                                                                                           {List
                                                                                                                              integer}
                                                                                                                           MinValue
                                                                                                                           ((let
                                                                                                                                a
                                                                                                                                  = List
                                                                                                                                      integer
                                                                                                                              in
                                                                                                                              \(c :
                                                                                                                                  integer ->
                                                                                                                                  a ->
                                                                                                                                  a)
                                                                                                                               (n :
                                                                                                                                  a) ->
                                                                                                                                c
                                                                                                                                  13
                                                                                                                                  (c
                                                                                                                                     0
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
                                                                                                                                 {integer})))
                                                                                                                        (c
                                                                                                                           (Tuple2
                                                                                                                              {PredKey}
                                                                                                                              {List
                                                                                                                                 integer}
                                                                                                                              MaxValue
                                                                                                                              ((let
                                                                                                                                   a
                                                                                                                                     = List
                                                                                                                                         integer
                                                                                                                                 in
                                                                                                                                 \(c :
                                                                                                                                     integer ->
                                                                                                                                     a ->
                                                                                                                                     a)
                                                                                                                                  (n :
                                                                                                                                     a) ->
                                                                                                                                   c
                                                                                                                                     37
                                                                                                                                     n)
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
                                                                                                                                    {integer})))
                                                                                                                           n)))))
                                                                                                        (c
                                                                                                           (Tuple2
                                                                                                              {integer}
                                                                                                              {ParamValue}
                                                                                                              33
                                                                                                              (ParamRational
                                                                                                                 ((let
                                                                                                                      a
                                                                                                                        = Tuple2
                                                                                                                            PredKey
                                                                                                                            (List
                                                                                                                               Rational)
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
                                                                                                                             PredKey
                                                                                                                             (List
                                                                                                                                Rational) ->
                                                                                                                           a ->
                                                                                                                           a)
                                                                                                                        (n :
                                                                                                                           a) ->
                                                                                                                         c
                                                                                                                           (Tuple2
                                                                                                                              {PredKey}
                                                                                                                              {List
                                                                                                                                 Rational}
                                                                                                                              MinValue
                                                                                                                              ((let
                                                                                                                                   a
                                                                                                                                     = List
                                                                                                                                         Rational
                                                                                                                                 in
                                                                                                                                 \(c :
                                                                                                                                     Rational ->
                                                                                                                                     a ->
                                                                                                                                     a)
                                                                                                                                  (n :
                                                                                                                                     a) ->
                                                                                                                                   c
                                                                                                                                     (unsafeRatio
                                                                                                                                        0
                                                                                                                                        1)
                                                                                                                                     n)
                                                                                                                                 (\(ds :
                                                                                                                                      Rational)
                                                                                                                                   (ds :
                                                                                                                                      List
                                                                                                                                        Rational) ->
                                                                                                                                    Cons
                                                                                                                                      {Rational}
                                                                                                                                      ds
                                                                                                                                      ds)
                                                                                                                                 (Nil
                                                                                                                                    {Rational})))
                                                                                                                           (c
                                                                                                                              (Tuple2
                                                                                                                                 {PredKey}
                                                                                                                                 {List
                                                                                                                                    Rational}
                                                                                                                                 MaxValue
                                                                                                                                 ((let
                                                                                                                                      a
                                                                                                                                        = List
                                                                                                                                            Rational
                                                                                                                                    in
                                                                                                                                    \(c :
                                                                                                                                        Rational ->
                                                                                                                                        a ->
                                                                                                                                        a)
                                                                                                                                     (n :
                                                                                                                                        a) ->
                                                                                                                                      c
                                                                                                                                        (unsafeRatio
                                                                                                                                           1000
                                                                                                                                           1)
                                                                                                                                        n)
                                                                                                                                    (\(ds :
                                                                                                                                         Rational)
                                                                                                                                      (ds :
                                                                                                                                         List
                                                                                                                                           Rational) ->
                                                                                                                                       Cons
                                                                                                                                         {Rational}
                                                                                                                                         ds
                                                                                                                                         ds)
                                                                                                                                    (Nil
                                                                                                                                       {Rational})))
                                                                                                                              n)))))
                                                                                                           n)))))))))))))))))))))))))))))))
  in
  \(ds : data) ->
    Maybe_match
      {List (Tuple2 data data)}
      (let
        !ds : pair integer (list data)
          = unConstrData
              (headList
                 {data}
                 (tailList
                    {data}
                    (tailList
                       {data}
                       (case
                          (list data)
                          (unConstrData
                             (let
                               !si : pair integer (list data)
                                 = unConstrData
                                     (headList
                                        {data}
                                        (tailList
                                           {data}
                                           (tailList
                                              {data}
                                              (case
                                                 (list data)
                                                 (unConstrData ds)
                                                 [ (\(l : integer)
                                                     (r : list data) ->
                                                      r) ]))))
                             in
                             case
                               (all dead. data)
                               (equalsInteger
                                  5
                                  (case
                                     integer
                                     si
                                     [(\(l : integer) (r : list data) -> l)]))
                               [ (/\dead -> error {data})
                               , (/\dead ->
                                    headList
                                      {data}
                                      (tailList
                                         {data}
                                         (case
                                            (list data)
                                            si
                                            [ (\(l : integer) (r : list data) ->
                                                 r) ]))) ]
                               {all dead. dead}))
                          [(\(l : integer) (r : list data) -> r)]))))
        !x : integer = case integer ds [(\(l : integer) (r : list data) -> l)]
      in
      case
        (all dead. Maybe (List (Tuple2 data data)))
        (equalsInteger 0 x)
        [ (/\dead ->
             case
               (all dead. Maybe (List (Tuple2 data data)))
               (equalsInteger 2 x)
               [ (/\dead -> error {Maybe (List (Tuple2 data data))})
               , (/\dead -> Nothing {List (Tuple2 data data)}) ]
               {all dead. dead})
        , (/\dead ->
             Just
               {List (Tuple2 data data)}
               (let
                 !d : data
                   = headList
                       {data}
                       (tailList
                          {data}
                          (case
                             (list data)
                             ds
                             [(\(l : integer) (r : list data) -> r)]))
               in
               matchData_go (unMapData d))) ]
        {all dead. dead})
      {all dead. unit}
      (\(cparams : List (Tuple2 data data)) ->
         /\dead ->
           case
             (all dead. unit)
             (fun cparams)
             [(/\dead -> error {unit}), (/\dead -> ())]
             {all dead. dead})
      (/\dead -> ())
      {all dead. dead})