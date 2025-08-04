letrec
  data (List :: * -> *) a | List_match where
    Nil : List a
    Cons : a -> List a -> List a
in
letrec
  !go : List integer -> integer -> List integer
    = \(acc : List integer) (n : integer) ->
        let
          !x : integer = quotientInteger n 10
        in
        case
          (all dead. List integer)
          (equalsInteger 0 x)
          [ (/\dead -> go (Cons {integer} (remainderInteger n 10) acc) x)
          , (/\dead -> Cons {integer} (remainderInteger n 10) acc) ]
          {all dead. dead}
in
letrec
  !go :
     List integer -> List string -> List string
    = \(ds : List integer) ->
        List_match
          {integer}
          ds
          {all dead. List string -> List string}
          (/\dead -> \(x : List string) -> x)
          (\(x : integer)
            (xs : List integer) ->
             /\dead ->
               let
                 !acc : List string -> List string = go xs
               in
               \(eta : List string) ->
                 Cons
                   {string}
                   (case
                      (all dead. string)
                      (equalsInteger 0 x)
                      [ (/\dead ->
                           case
                             (all dead. string)
                             (equalsInteger 1 x)
                             [ (/\dead ->
                                  case
                                    (all dead. string)
                                    (equalsInteger 2 x)
                                    [ (/\dead ->
                                         case
                                           (all dead. string)
                                           (equalsInteger 3 x)
                                           [ (/\dead ->
                                                case
                                                  (all dead. string)
                                                  (equalsInteger 4 x)
                                                  [ (/\dead ->
                                                       case
                                                         (all dead. string)
                                                         (equalsInteger 5 x)
                                                         [ (/\dead ->
                                                              case
                                                                (all dead.
                                                                   string)
                                                                (equalsInteger
                                                                   6
                                                                   x)
                                                                [ (/\dead ->
                                                                     case
                                                                       (all dead.
                                                                          string)
                                                                       (equalsInteger
                                                                          7
                                                                          x)
                                                                       [ (/\dead ->
                                                                            case
                                                                              (all dead.
                                                                                 string)
                                                                              (equalsInteger
                                                                                 8
                                                                                 x)
                                                                              [ (/\dead ->
                                                                                   case
                                                                                     string
                                                                                     (equalsInteger
                                                                                        9
                                                                                        x)
                                                                                     [ "<invalid digit>"
                                                                                     , "9" ])
                                                                              , (/\dead ->
                                                                                   "8") ]
                                                                              {all dead.
                                                                                 dead})
                                                                       , (/\dead ->
                                                                            "7") ]
                                                                       {all dead.
                                                                          dead})
                                                                , (/\dead ->
                                                                     "6") ]
                                                                {all dead.
                                                                   dead})
                                                         , (/\dead -> "5") ]
                                                         {all dead. dead})
                                                  , (/\dead -> "4") ]
                                                  {all dead. dead})
                                           , (/\dead -> "3") ]
                                           {all dead. dead})
                                    , (/\dead -> "2") ]
                                    {all dead. dead})
                             , (/\dead -> "1") ]
                             {all dead. dead})
                      , (/\dead -> "0") ]
                      {all dead. dead})
                   (acc eta))
          {all dead. dead}
in
letrec
  !`$fShowBuiltinByteString_$cshowsPrec` :
     integer -> integer -> List string -> List string
    = \(p : integer) (n : integer) ->
        case
          (all dead. List string -> List string)
          (lessThanInteger n 0)
          [ (/\dead -> go (go (Nil {integer}) n))
          , (/\dead ->
               \(eta : List string) ->
                 Cons
                   {string}
                   "-"
                   (`$fShowBuiltinByteString_$cshowsPrec`
                      p
                      (subtractInteger 0 n)
                      eta)) ]
          {all dead. dead}
in
let
  !toHex : integer -> List string -> List string
    = \(x : integer) ->
        case
          (all dead. List string -> List string)
          (lessThanEqualsInteger x 9)
          [ (/\dead ->
               case
                 (all dead. List string -> List string)
                 (equalsInteger 10 x)
                 [ (/\dead ->
                      case
                        (all dead. List string -> List string)
                        (equalsInteger 11 x)
                        [ (/\dead ->
                             case
                               (all dead. List string -> List string)
                               (equalsInteger 12 x)
                               [ (/\dead ->
                                    case
                                      (all dead. List string -> List string)
                                      (equalsInteger 13 x)
                                      [ (/\dead ->
                                           case
                                             (all dead.
                                                List string -> List string)
                                             (equalsInteger 14 x)
                                             [ (/\dead ->
                                                  case
                                                    (List string -> List string)
                                                    (equalsInteger 15 x)
                                                    [ (\(ds : List string) ->
                                                         Cons
                                                           {string}
                                                           "<invalid byte>"
                                                           ds)
                                                    , (\(ds : List string) ->
                                                         Cons
                                                           {string}
                                                           "f"
                                                           ds) ])
                                             , (/\dead ->
                                                  \(ds : List string) ->
                                                    Cons {string} "e" ds) ]
                                             {all dead. dead})
                                      , (/\dead ->
                                           \(ds : List string) ->
                                             Cons {string} "d" ds) ]
                                      {all dead. dead})
                               , (/\dead ->
                                    \(ds : List string) ->
                                      Cons {string} "c" ds) ]
                               {all dead. dead})
                        , (/\dead ->
                             \(ds : List string) -> Cons {string} "b" ds) ]
                        {all dead. dead})
                 , (/\dead -> \(ds : List string) -> Cons {string} "a" ds) ]
                 {all dead. dead})
          , (/\dead -> `$fShowBuiltinByteString_$cshowsPrec` 0 x) ]
          {all dead. dead}
in
letrec
  !go : List integer -> List string -> List string
    = \(ds : List integer) ->
        List_match
          {integer}
          ds
          {all dead. List string -> List string}
          (/\dead -> \(x : List string) -> x)
          (\(x : integer) (xs : List integer) ->
             /\dead ->
               let
                 !acc : List string -> List string = go xs
               in
               \(eta : List string) ->
                 (let
                     !x : integer
                       = indexByteString #5468697320697320616e206578616d706c65 x
                   in
                   \(eta : List string) ->
                     toHex (divideInteger x 16) (toHex (modInteger x 16) eta))
                   (acc eta))
          {all dead. dead}
in
let
  !ifThenElse : all a. bool -> a -> a -> a
    = /\a -> \(b : bool) (x : a) (y : a) -> case a b [y, x]
in
letrec
  !`$fEnumBool_$cenumFromTo` : integer -> integer -> List integer
    = \(x : integer) (lim : integer) ->
        case
          (all dead. List integer)
          (ifThenElse {bool} (lessThanEqualsInteger x lim) False True)
          [ (/\dead ->
               Cons
                 {integer}
                 x
                 (`$fEnumBool_$cenumFromTo` (addInteger 1 x) lim))
          , (/\dead -> Nil {integer}) ]
          {all dead. dead}
in
let
  data (Tuple2 :: * -> * -> *) a b | Tuple2_match where
    Tuple2 : a -> b -> Tuple2 a b
in
letrec
  !go : integer -> List string -> Tuple2 (List string) (List string)
    = \(ds : integer) (ds : List string) ->
        List_match
          {string}
          ds
          {all dead. Tuple2 (List string) (List string)}
          (/\dead ->
             Tuple2 {List string} {List string} (Nil {string}) (Nil {string}))
          (\(y : string) (ys : List string) ->
             /\dead ->
               case
                 (all dead. Tuple2 (List string) (List string))
                 (equalsInteger 1 ds)
                 [ (/\dead ->
                      Tuple2_match
                        {List string}
                        {List string}
                        (go (subtractInteger ds 1) ys)
                        {Tuple2 (List string) (List string)}
                        (\(zs : List string) (ws : List string) ->
                           Tuple2
                             {List string}
                             {List string}
                             (Cons {string} y zs)
                             ws))
                 , (/\dead ->
                      Tuple2
                        {List string}
                        {List string}
                        ((let
                             a = List string
                           in
                           \(c : string -> a -> a) (n : a) -> c y n)
                           (\(ds : string) (ds : List string) ->
                              Cons {string} ds ds)
                           (Nil {string}))
                        ys) ]
                 {all dead. dead})
          {all dead. dead}
in
letrec
  !go : List string -> integer
    = \(ds : List string) ->
        List_match
          {string}
          ds
          {integer}
          0
          (\(ds : string) (xs : List string) -> addInteger 1 (go xs))
in
letrec
  !concatBuiltinStrings : List string -> string
    = \(ds : List string) ->
        List_match
          {string}
          ds
          {string}
          ""
          (\(x : string) (ds : List string) ->
             List_match
               {string}
               ds
               {all dead. string}
               (/\dead -> x)
               (\(ipv : string) (ipv : List string) ->
                  /\dead ->
                    Tuple2_match
                      {List string}
                      {List string}
                      (let
                        !n : integer = divideInteger (go ds) 2
                      in
                      case
                        (all dead. Tuple2 (List string) (List string))
                        (lessThanEqualsInteger n 0)
                        [ (/\dead -> go n ds)
                        , (/\dead ->
                             Tuple2
                               {List string}
                               {List string}
                               (Nil {string})
                               ds) ]
                        {all dead. dead})
                      {string}
                      (\(ipv : List string) (ipv : List string) ->
                         appendString
                           (concatBuiltinStrings ipv)
                           (concatBuiltinStrings ipv)))
               {all dead. dead})
in
let
  !`$fShowInteger_$cshow` : integer -> string
    = \(x : integer) ->
        concatBuiltinStrings
          (`$fShowBuiltinByteString_$cshowsPrec` 0 x (Nil {string}))
  data (Show :: * -> *) a | Show_match where
    CConsShow :
      (integer -> a -> List string -> List string) -> (a -> string) -> Show a
  !`$fShowInteger` : Show integer
    = CConsShow
        {integer}
        `$fShowBuiltinByteString_$cshowsPrec`
        `$fShowInteger_$cshow`
  data (Tuple5 :: * -> * -> * -> * -> * -> *) a b c d e | Tuple5_match where
    Tuple5 : a -> b -> c -> d -> e -> Tuple5 a b c d e
  !showsPrec : all a. Show a -> integer -> a -> List string -> List string
    = /\a ->
        \(v : Show a) ->
          Show_match
            {a}
            v
            {integer -> a -> List string -> List string}
            (\(v : integer -> a -> List string -> List string)
              (v : a -> string) ->
               v)
  !a : integer
    = trace {integer} (`$fShowInteger_$cshow` -1234567890) -1234567890
  !b : integer = trace {integer} "This is an example" a
  !c : integer
    = trace
        {integer}
        (concatBuiltinStrings
           (go (`$fEnumBool_$cenumFromTo` 0 17) (Nil {string})))
        b
  !d : integer
    = trace
        {integer}
        (case
           string
           (ifThenElse {bool} (lessThanEqualsInteger c 0) False True)
           ["False", "True"])
        c
  !e : integer
    = trace
        {integer}
        (let
          !x : List integer
            = (let
                  a = List integer
                in
                \(c : integer -> a -> a) (n : a) -> c a (c b (c c (c d n))))
                (\(ds : integer) (ds : List integer) -> Cons {integer} ds ds)
                (Nil {integer})
        in
        concatBuiltinStrings
          ((let
               !showElem : integer -> List string -> List string
                 = showsPrec {integer} `$fShowInteger` 0
             in
             letrec
               !go : List integer -> List string -> List string
                 = \(ds : List integer) ->
                     List_match
                       {integer}
                       ds
                       {all dead. List string -> List string}
                       (/\dead -> \(x : List string) -> x)
                       (\(x : integer) (xs : List integer) ->
                          /\dead ->
                            let
                              !acc : List string -> List string = go xs
                            in
                            \(eta : List string) ->
                              Cons {string} "," (showElem x (acc eta)))
                       {all dead. dead}
             in
             List_match
               {integer}
               x
               {List string -> List string}
               (\(ds : List string) -> Cons {string} "[]" ds)
               (\(x : integer) (xs : List integer) (eta : List string) ->
                  Cons
                    {string}
                    "["
                    (showElem x (go xs (Cons {string} "]" eta)))))
             (Nil {string})))
        d
in
multiplyInteger
  2
  (trace
     {integer}
     (concatBuiltinStrings
        (Cons
           {string}
           "("
           (showsPrec
              {integer}
              `$fShowInteger`
              0
              a
              (Cons
                 {string}
                 ","
                 (showsPrec
                    {integer}
                    `$fShowInteger`
                    0
                    b
                    (Cons
                       {string}
                       ","
                       (showsPrec
                          {integer}
                          `$fShowInteger`
                          0
                          c
                          (Cons
                             {string}
                             ","
                             (showsPrec
                                {integer}
                                `$fShowInteger`
                                0
                                d
                                (Cons
                                   {string}
                                   ","
                                   (showsPrec
                                      {integer}
                                      `$fShowInteger`
                                      0
                                      e
                                      (Cons
                                         {string}
                                         ")"
                                         (Nil {string})))))))))))))
     e)