let
  data (Tuple2 :: * -> * -> *) a b | Tuple2_match where
    Tuple2 : a -> b -> Tuple2 a b
in
letrec
  data (List :: * -> *) a | List_match where
    Nil : List a
    Cons : a -> List a -> List a
in
letrec
  !go : List (Tuple2 bytestring integer) -> bool
    = \(ds : List (Tuple2 bytestring integer)) ->
        List_match
          {Tuple2 bytestring integer}
          ds
          {bool}
          True
          (\(ds : Tuple2 bytestring integer)
            (xs : List (Tuple2 bytestring integer)) ->
             Tuple2_match
               {bytestring}
               {integer}
               ds
               {bool}
               (\(ds : bytestring) (x : integer) ->
                  case
                    (all dead. bool)
                    (equalsInteger 0 x)
                    [(/\dead -> False), (/\dead -> go xs)]
                    {all dead. dead}))
in
let
  !ifThenElse : all a. bool -> a -> a -> a
    = /\a -> \(b : bool) (x : a) (y : a) -> case a b [y, x]
  data (These :: * -> * -> *) a b | These_match where
    That : b -> These a b
    These : a -> b -> These a b
    This : a -> These a b
in
letrec
  !go :
     List
       (Tuple2
          bytestring
          ((\k v -> List (Tuple2 k v)) bytestring (These integer integer))) ->
     bool
    = \(ds :
          List
            (Tuple2
               bytestring
               ((\k v -> List (Tuple2 k v))
                  bytestring
                  (These integer integer)))) ->
        List_match
          {Tuple2
             bytestring
             ((\k v -> List (Tuple2 k v)) bytestring (These integer integer))}
          ds
          {bool}
          True
          (\(ds :
               Tuple2
                 bytestring
                 ((\k v -> List (Tuple2 k v))
                    bytestring
                    (These integer integer)))
            (xs :
               List
                 (Tuple2
                    bytestring
                    ((\k v -> List (Tuple2 k v))
                       bytestring
                       (These integer integer)))) ->
             letrec
               !go : List (Tuple2 bytestring (These integer integer)) -> bool
                 = \(ds : List (Tuple2 bytestring (These integer integer))) ->
                     List_match
                       {Tuple2 bytestring (These integer integer)}
                       ds
                       {all dead. bool}
                       (/\dead -> go xs)
                       (\(ds : Tuple2 bytestring (These integer integer))
                         (xs :
                            List (Tuple2 bytestring (These integer integer))) ->
                          /\dead ->
                            Tuple2_match
                              {bytestring}
                              {These integer integer}
                              ds
                              {bool}
                              (\(ds : bytestring) (x : These integer integer) ->
                                 case
                                   (all dead. bool)
                                   (These_match
                                      {integer}
                                      {integer}
                                      x
                                      {bool}
                                      (\(b : integer) ->
                                         ifThenElse
                                           {bool}
                                           (lessThanInteger 0 b)
                                           False
                                           True)
                                      (\(a : integer) (b : integer) ->
                                         ifThenElse
                                           {bool}
                                           (lessThanInteger a b)
                                           False
                                           True)
                                      (\(a : integer) ->
                                         ifThenElse
                                           {bool}
                                           (lessThanInteger a 0)
                                           False
                                           True))
                                   [(/\dead -> False), (/\dead -> go xs)]
                                   {all dead. dead}))
                       {all dead. dead}
             in
             Tuple2_match
               {bytestring}
               {(\k v -> List (Tuple2 k v)) bytestring (These integer integer)}
               ds
               {bool}
               (\(ds : bytestring)
                 (x :
                    (\k v -> List (Tuple2 k v))
                      bytestring
                      (These integer integer)) ->
                  go x))
in
letrec
  !go :
     List (Tuple2 bytestring integer) ->
     List (Tuple2 bytestring (These integer integer))
    = \(ds : List (Tuple2 bytestring integer)) ->
        List_match
          {Tuple2 bytestring integer}
          ds
          {all dead. List (Tuple2 bytestring (These integer integer))}
          (/\dead -> Nil {Tuple2 bytestring (These integer integer)})
          (\(x : Tuple2 bytestring integer)
            (xs : List (Tuple2 bytestring integer)) ->
             /\dead ->
               Cons
                 {Tuple2 bytestring (These integer integer)}
                 (Tuple2_match
                    {bytestring}
                    {integer}
                    x
                    {Tuple2 bytestring (These integer integer)}
                    (\(c : bytestring) (a : integer) ->
                       Tuple2
                         {bytestring}
                         {These integer integer}
                         c
                         (This {integer} {integer} a)))
                 (go xs))
          {all dead. dead}
in
letrec
  !go :
     List (Tuple2 bytestring integer) ->
     List (Tuple2 bytestring (These integer integer))
    = \(ds : List (Tuple2 bytestring integer)) ->
        List_match
          {Tuple2 bytestring integer}
          ds
          {all dead. List (Tuple2 bytestring (These integer integer))}
          (/\dead -> Nil {Tuple2 bytestring (These integer integer)})
          (\(x : Tuple2 bytestring integer)
            (xs : List (Tuple2 bytestring integer)) ->
             /\dead ->
               Cons
                 {Tuple2 bytestring (These integer integer)}
                 (Tuple2_match
                    {bytestring}
                    {integer}
                    x
                    {Tuple2 bytestring (These integer integer)}
                    (\(c : bytestring) (a : integer) ->
                       Tuple2
                         {bytestring}
                         {These integer integer}
                         c
                         (That {integer} {integer} a)))
                 (go xs))
          {all dead. dead}
in
let
  !equalsByteString : bytestring -> bytestring -> bool
    = \(x : bytestring) (y : bytestring) -> equalsByteString x y
  !union :
     all k v r.
       (\a -> a -> a -> bool) k ->
       (\k v -> List (Tuple2 k v)) k v ->
       (\k v -> List (Tuple2 k v)) k r ->
       (\k v -> List (Tuple2 k v)) k (These v r)
    = /\k v r ->
        letrec
          !go : List (Tuple2 k r) -> List (Tuple2 k (These v r))
            = \(ds : List (Tuple2 k r)) ->
                List_match
                  {Tuple2 k r}
                  ds
                  {all dead. List (Tuple2 k (These v r))}
                  (/\dead -> Nil {Tuple2 k (These v r)})
                  (\(x : Tuple2 k r) (xs : List (Tuple2 k r)) ->
                     /\dead ->
                       Cons
                         {Tuple2 k (These v r)}
                         (Tuple2_match
                            {k}
                            {r}
                            x
                            {Tuple2 k (These v r)}
                            (\(c : k) (a : r) ->
                               Tuple2 {k} {These v r} c (That {v} {r} a)))
                         (go xs))
                  {all dead. dead}
        in
        \(`$dEq` : (\a -> a -> a -> bool) k)
         (ds : (\k v -> List (Tuple2 k v)) k v)
         (ds : (\k v -> List (Tuple2 k v)) k r) ->
          letrec
            !go : List (Tuple2 k v) -> List (Tuple2 k (These v r))
              = \(ds : List (Tuple2 k v)) ->
                  List_match
                    {Tuple2 k v}
                    ds
                    {all dead. List (Tuple2 k (These v r))}
                    (/\dead -> Nil {Tuple2 k (These v r)})
                    (\(x : Tuple2 k v) (xs : List (Tuple2 k v)) ->
                       /\dead ->
                         Cons
                           {Tuple2 k (These v r)}
                           (Tuple2_match
                              {k}
                              {v}
                              x
                              {Tuple2 k (These v r)}
                              (\(c : k) (i : v) ->
                                 letrec
                                   !go : List (Tuple2 k r) -> These v r
                                     = \(ds : List (Tuple2 k r)) ->
                                         List_match
                                           {Tuple2 k r}
                                           ds
                                           {all dead. These v r}
                                           (/\dead -> This {v} {r} i)
                                           (\(ds : Tuple2 k r)
                                             (xs' : List (Tuple2 k r)) ->
                                              /\dead ->
                                                Tuple2_match
                                                  {k}
                                                  {r}
                                                  ds
                                                  {These v r}
                                                  (\(c' : k) (i : r) ->
                                                     case
                                                       (all dead. These v r)
                                                       (`$dEq` c' c)
                                                       [ (/\dead -> go xs')
                                                       , (/\dead ->
                                                            These {v} {r} i i) ]
                                                       {all dead. dead}))
                                           {all dead. dead}
                                 in
                                 Tuple2 {k} {These v r} c (go ds)))
                           (go xs))
                    {all dead. dead}
          in
          let
            !rs' : List (Tuple2 k r)
              = (let
                    a = Tuple2 k r
                  in
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
                    \(eta : List a) -> go eta)
                  (\(ds : Tuple2 k r) ->
                     Tuple2_match
                       {k}
                       {r}
                       ds
                       {bool}
                       (\(c : k) ->
                          letrec
                            !go : List (Tuple2 k v) -> bool
                              = \(ds : List (Tuple2 k v)) ->
                                  List_match
                                    {Tuple2 k v}
                                    ds
                                    {bool}
                                    True
                                    (\(x : Tuple2 k v)
                                      (xs : List (Tuple2 k v)) ->
                                       Tuple2_match
                                         {k}
                                         {v}
                                         x
                                         {bool}
                                         (\(c' : k) (ds : v) ->
                                            case
                                              (all dead. bool)
                                              (`$dEq` c' c)
                                              [ (/\dead -> go xs)
                                              , (/\dead -> False) ]
                                              {all dead. dead}))
                          in
                          \(ds : r) -> go ds))
                  ds
            !rs'' : List (Tuple2 k (These v r)) = go rs'
          in
          letrec
            !go : List (Tuple2 k (These v r)) -> List (Tuple2 k (These v r))
              = \(ds : List (Tuple2 k (These v r))) ->
                  List_match
                    {Tuple2 k (These v r)}
                    ds
                    {all dead. List (Tuple2 k (These v r))}
                    (/\dead -> rs'')
                    (\(x : Tuple2 k (These v r))
                      (xs : List (Tuple2 k (These v r))) ->
                       /\dead -> Cons {Tuple2 k (These v r)} x (go xs))
                    {all dead. dead}
          in
          let
            !ls' : List (Tuple2 k (These v r)) = go ds
          in
          go ls'
in
letrec
  !go :
     List
       (Tuple2
          bytestring
          (These
             ((\k v -> List (Tuple2 k v)) bytestring integer)
             ((\k v -> List (Tuple2 k v)) bytestring integer))) ->
     List
       (Tuple2
          bytestring
          ((\k v -> List (Tuple2 k v)) bytestring (These integer integer)))
    = \(ds :
          List
            (Tuple2
               bytestring
               (These
                  ((\k v -> List (Tuple2 k v)) bytestring integer)
                  ((\k v -> List (Tuple2 k v)) bytestring integer)))) ->
        List_match
          {Tuple2
             bytestring
             (These
                ((\k v -> List (Tuple2 k v)) bytestring integer)
                ((\k v -> List (Tuple2 k v)) bytestring integer))}
          ds
          {all dead.
             List
               (Tuple2
                  bytestring
                  ((\k v -> List (Tuple2 k v))
                     bytestring
                     (These integer integer)))}
          (/\dead ->
             Nil
               {Tuple2
                  bytestring
                  ((\k v -> List (Tuple2 k v))
                     bytestring
                     (These integer integer))})
          (\(x :
               Tuple2
                 bytestring
                 (These
                    ((\k v -> List (Tuple2 k v)) bytestring integer)
                    ((\k v -> List (Tuple2 k v)) bytestring integer)))
            (xs :
               List
                 (Tuple2
                    bytestring
                    (These
                       ((\k v -> List (Tuple2 k v)) bytestring integer)
                       ((\k v -> List (Tuple2 k v)) bytestring integer)))) ->
             /\dead ->
               Cons
                 {Tuple2
                    bytestring
                    ((\k v -> List (Tuple2 k v))
                       bytestring
                       (These integer integer))}
                 (Tuple2_match
                    {bytestring}
                    {These
                       ((\k v -> List (Tuple2 k v)) bytestring integer)
                       ((\k v -> List (Tuple2 k v)) bytestring integer)}
                    x
                    {Tuple2
                       bytestring
                       ((\k v -> List (Tuple2 k v))
                          bytestring
                          (These integer integer))}
                    (\(c : bytestring)
                      (a :
                         These
                           ((\k v -> List (Tuple2 k v)) bytestring integer)
                           ((\k v -> List (Tuple2 k v)) bytestring integer)) ->
                       Tuple2
                         {bytestring}
                         {(\k v -> List (Tuple2 k v))
                            bytestring
                            (These integer integer)}
                         c
                         (These_match
                            {(\k v -> List (Tuple2 k v)) bytestring integer}
                            {(\k v -> List (Tuple2 k v)) bytestring integer}
                            a
                            {(\k v -> List (Tuple2 k v))
                               bytestring
                               (These integer integer)}
                            (\(b :
                                 (\k v -> List (Tuple2 k v))
                                   bytestring
                                   integer) ->
                               go b)
                            (\(a :
                                 (\k v -> List (Tuple2 k v)) bytestring integer)
                              (b :
                                 (\k v -> List (Tuple2 k v))
                                   bytestring
                                   integer) ->
                               union
                                 {bytestring}
                                 {integer}
                                 {integer}
                                 equalsByteString
                                 a
                                 b)
                            (\(a :
                                 (\k v -> List (Tuple2 k v))
                                   bytestring
                                   integer) ->
                               go a))))
                 (go xs))
          {all dead. dead}
in
let
  !unordEqWith :
     all k v.
       (\a -> a -> a -> bool) k ->
       (v -> bool) ->
       (v -> v -> bool) ->
       List (Tuple2 k v) ->
       List (Tuple2 k v) ->
       bool
    = /\k v ->
        \(`$dEq` : (\a -> a -> a -> bool) k)
         (is : v -> bool) ->
          letrec
            !go : List (Tuple2 k v) -> bool
              = \(ds : List (Tuple2 k v)) ->
                  List_match
                    {Tuple2 k v}
                    ds
                    {bool}
                    True
                    (\(x : Tuple2 k v) (xs : List (Tuple2 k v)) ->
                       Tuple2_match
                         {k}
                         {v}
                         x
                         {bool}
                         (\(ipv : k) (ipv : v) ->
                            case
                              (all dead. bool)
                              (is ipv)
                              [(/\dead -> False), (/\dead -> go xs)]
                              {all dead. dead}))
          in
          letrec
            !go : List (Tuple2 k v) -> bool
              = \(ds : List (Tuple2 k v)) ->
                  List_match
                    {Tuple2 k v}
                    ds
                    {bool}
                    True
                    (\(x : Tuple2 k v) (xs : List (Tuple2 k v)) ->
                       Tuple2_match
                         {k}
                         {v}
                         x
                         {bool}
                         (\(ipv : k) (ipv : v) ->
                            case
                              (all dead. bool)
                              (is ipv)
                              [(/\dead -> False), (/\dead -> go xs)]
                              {all dead. dead}))
          in
          \(eqV : v -> v -> bool) ->
            letrec
              !goBoth :
                 List (Tuple2 k v) -> List (Tuple2 k v) -> bool
                = \(ds : List (Tuple2 k v))
                   (kvsR : List (Tuple2 k v)) ->
                    List_match
                      {Tuple2 k v}
                      ds
                      {all dead. bool}
                      (/\dead -> go kvsR)
                      (\(ipv : Tuple2 k v)
                        (ipv : List (Tuple2 k v)) ->
                         /\dead ->
                           List_match
                             {Tuple2 k v}
                             kvsR
                             {all dead. bool}
                             (/\dead -> go ds)
                             (\(ipv : Tuple2 k v)
                               (ipv : List (Tuple2 k v)) ->
                                /\dead ->
                                  Tuple2_match
                                    {k}
                                    {v}
                                    ipv
                                    {bool}
                                    (\(kL : k)
                                      (vL : v) ->
                                       letrec
                                         !goRight :
                                            List (Tuple2 k v) ->
                                            List (Tuple2 k v) ->
                                            bool
                                           = \(ds : List (Tuple2 k v))
                                              (ds : List (Tuple2 k v)) ->
                                               List_match
                                                 {Tuple2 k v}
                                                 ds
                                                 {bool}
                                                 False
                                                 (\(kvR : Tuple2 k v)
                                                   (kvsR' :
                                                      List (Tuple2 k v)) ->
                                                    Tuple2_match
                                                      {k}
                                                      {v}
                                                      kvR
                                                      {bool}
                                                      (\(kR : k)
                                                        (vR : v) ->
                                                         case
                                                           (all dead. bool)
                                                           (is vR)
                                                           [ (/\dead ->
                                                                case
                                                                  (all dead.
                                                                     bool)
                                                                  (`$dEq` kL kR)
                                                                  [ (/\dead ->
                                                                       goRight
                                                                         (Cons
                                                                            {Tuple2
                                                                               k
                                                                               v}
                                                                            kvR
                                                                            ds)
                                                                         kvsR')
                                                                  , (/\dead ->
                                                                       case
                                                                         (all dead.
                                                                            bool)
                                                                         (eqV
                                                                            vL
                                                                            vR)
                                                                         [ (/\dead ->
                                                                              False)
                                                                         , (/\dead ->
                                                                              goBoth
                                                                                ipv
                                                                                ((let
                                                                                     a
                                                                                       = Tuple2
                                                                                           k
                                                                                           v
                                                                                   in
                                                                                   letrec
                                                                                     !rev :
                                                                                        List
                                                                                          a ->
                                                                                        List
                                                                                          a ->
                                                                                        List
                                                                                          a
                                                                                       = \(ds :
                                                                                             List
                                                                                               a)
                                                                                          (a :
                                                                                             List
                                                                                               a) ->
                                                                                           List_match
                                                                                             {a}
                                                                                             ds
                                                                                             {all dead.
                                                                                                List
                                                                                                  a}
                                                                                             (/\dead ->
                                                                                                a)
                                                                                             (\(x :
                                                                                                  a)
                                                                                               (xs :
                                                                                                  List
                                                                                                    a) ->
                                                                                                /\dead ->
                                                                                                  rev
                                                                                                    xs
                                                                                                    (Cons
                                                                                                       {a}
                                                                                                       x
                                                                                                       a))
                                                                                             {all dead.
                                                                                                dead}
                                                                                   in
                                                                                   \(eta :
                                                                                       List
                                                                                         a)
                                                                                    (eta :
                                                                                       List
                                                                                         a) ->
                                                                                     rev
                                                                                       eta
                                                                                       eta)
                                                                                   ds
                                                                                   kvsR')) ]
                                                                         {all dead.
                                                                            dead}) ]
                                                                  {all dead.
                                                                     dead})
                                                           , (/\dead ->
                                                                goRight
                                                                  ds
                                                                  kvsR') ]
                                                           {all dead. dead}))
                                       in
                                       Tuple2_match
                                         {k}
                                         {v}
                                         ipv
                                         {bool}
                                         (\(kR : k)
                                           (vR : v) ->
                                            case
                                              (all dead. bool)
                                              (`$dEq` kL kR)
                                              [ (/\dead ->
                                                   case
                                                     (all dead. bool)
                                                     (is vL)
                                                     [ (/\dead ->
                                                          goRight
                                                            ((let
                                                                 a = Tuple2 k v
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
                                                                        k
                                                                        v ->
                                                                      a ->
                                                                      a)
                                                                   (n : a) ->
                                                                    case
                                                                      (all dead.
                                                                         a)
                                                                      (is vR)
                                                                      [ (/\dead ->
                                                                           c
                                                                             ipv
                                                                             n)
                                                                      , (/\dead ->
                                                                           n) ]
                                                                      {all dead.
                                                                         dead}))
                                                            ipv)
                                                     , (/\dead ->
                                                          goBoth ipv kvsR) ]
                                                     {all dead. dead})
                                              , (/\dead ->
                                                   case
                                                     (all dead. bool)
                                                     (eqV vL vR)
                                                     [ (/\dead -> False)
                                                     , (/\dead ->
                                                          goBoth ipv ipv) ]
                                                     {all dead. dead}) ]
                                              {all dead. dead})))
                             {all dead. dead})
                      {all dead. dead}
            in
            \(eta : List (Tuple2 k v)) (eta : List (Tuple2 k v)) ->
              goBoth eta eta
in
\(l :
    (\k v -> List (Tuple2 k v))
      bytestring
      ((\k v -> List (Tuple2 k v)) bytestring integer))
 (r :
    (\k v -> List (Tuple2 k v))
      bytestring
      ((\k v -> List (Tuple2 k v)) bytestring integer)) ->
  case
    (all dead. bool)
    (let
      !m :
         List
           (Tuple2
              bytestring
              ((\k v -> List (Tuple2 k v)) bytestring (These integer integer)))
        = let
          !mp :
             List
               (Tuple2
                  bytestring
                  (These
                     ((\k v -> List (Tuple2 k v)) bytestring integer)
                     ((\k v -> List (Tuple2 k v)) bytestring integer)))
            = union
                {bytestring}
                {(\k v -> List (Tuple2 k v)) bytestring integer}
                {(\k v -> List (Tuple2 k v)) bytestring integer}
                equalsByteString
                l
                r
        in
        go mp
    in
    go m)
    [ (/\dead -> False)
    , (/\dead ->
         case
           bool
           (unordEqWith
              {bytestring}
              {(\k v -> List (Tuple2 k v)) bytestring integer}
              equalsByteString
              (\(ds : (\k v -> List (Tuple2 k v)) bytestring integer) -> go ds)
              (unordEqWith
                 {bytestring}
                 {integer}
                 equalsByteString
                 (\(v : integer) -> equalsInteger 0 v)
                 (\(x : integer) (y : integer) -> equalsInteger x y))
              l
              r)
           [True, False]) ]
    {all dead. dead}