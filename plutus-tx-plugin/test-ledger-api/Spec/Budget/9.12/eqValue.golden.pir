let
  data (Tuple :: * -> * -> *) a b | Tuple_match where
    Tuple2 : a -> b -> Tuple a b
in
letrec
  data (List :: * -> *) a | List_match where
    Nil : List a
    Cons : a -> List a -> List a
in
letrec
  !go : List (Tuple bytestring integer) -> bool
    = \(ds : List (Tuple bytestring integer)) ->
        List_match
          {Tuple bytestring integer}
          ds
          {bool}
          True
          (\(ds : Tuple bytestring integer)
            (xs : List (Tuple bytestring integer)) ->
             Tuple_match
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
  !equalsByteString : bytestring -> bytestring -> bool
    = \(x : bytestring) (y : bytestring) -> equalsByteString x y
  !unordEqWith :
     all k v.
       (\a -> a -> a -> bool) k ->
       (v -> bool) ->
       (v -> v -> bool) ->
       List (Tuple k v) ->
       List (Tuple k v) ->
       bool
    = /\k v ->
        \(`$dEq` : (\a -> a -> a -> bool) k)
         (is : v -> bool) ->
          letrec
            !go : List (Tuple k v) -> bool
              = \(ds : List (Tuple k v)) ->
                  List_match
                    {Tuple k v}
                    ds
                    {bool}
                    True
                    (\(x : Tuple k v) (xs : List (Tuple k v)) ->
                       Tuple_match
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
            !go : List (Tuple k v) -> bool
              = \(ds : List (Tuple k v)) ->
                  List_match
                    {Tuple k v}
                    ds
                    {bool}
                    True
                    (\(x : Tuple k v) (xs : List (Tuple k v)) ->
                       Tuple_match
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
                 List (Tuple k v) -> List (Tuple k v) -> bool
                = \(ds : List (Tuple k v))
                   (kvsR : List (Tuple k v)) ->
                    List_match
                      {Tuple k v}
                      ds
                      {all dead. bool}
                      (/\dead -> go kvsR)
                      (\(ipv : Tuple k v)
                        (ipv : List (Tuple k v)) ->
                         /\dead ->
                           List_match
                             {Tuple k v}
                             kvsR
                             {all dead. bool}
                             (/\dead -> go ds)
                             (\(ipv : Tuple k v)
                               (ipv : List (Tuple k v)) ->
                                /\dead ->
                                  Tuple_match
                                    {k}
                                    {v}
                                    ipv
                                    {bool}
                                    (\(kL : k)
                                      (vL : v) ->
                                       letrec
                                         !goRight :
                                            List (Tuple k v) ->
                                            List (Tuple k v) ->
                                            bool
                                           = \(ds : List (Tuple k v))
                                              (ds : List (Tuple k v)) ->
                                               List_match
                                                 {Tuple k v}
                                                 ds
                                                 {bool}
                                                 False
                                                 (\(kvR : Tuple k v)
                                                   (kvsR' : List (Tuple k v)) ->
                                                    Tuple_match
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
                                                                            {Tuple
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
                                                                                       = Tuple
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
                                       Tuple_match
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
                                                                 a = Tuple k v
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
                                                                      Tuple
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
            \(eta : List (Tuple k v)) (eta : List (Tuple k v)) -> goBoth eta eta
in
\(ds :
    (\k v -> List (Tuple k v))
      bytestring
      ((\k v -> List (Tuple k v)) bytestring integer))
 (ds :
    (\k v -> List (Tuple k v))
      bytestring
      ((\k v -> List (Tuple k v)) bytestring integer)) ->
  unordEqWith
    {bytestring}
    {(\k v -> List (Tuple k v)) bytestring integer}
    equalsByteString
    (\(ds : (\k v -> List (Tuple k v)) bytestring integer) -> go ds)
    (unordEqWith
       {bytestring}
       {integer}
       equalsByteString
       (\(v : integer) -> equalsInteger 0 v)
       (\(x : integer) (y : integer) -> equalsInteger x y))
    ds
    ds