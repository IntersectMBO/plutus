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
  !equalsByteString : bytestring -> bytestring -> bool
    = \(x : bytestring) (y : bytestring) -> equalsByteString x y
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
\(ds :
    (\k v -> List (Tuple2 k v))
      bytestring
      ((\k v -> List (Tuple2 k v)) bytestring integer))
 (ds :
    (\k v -> List (Tuple2 k v))
      bytestring
      ((\k v -> List (Tuple2 k v)) bytestring integer)) ->
  unordEqWith
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
    ds
    ds