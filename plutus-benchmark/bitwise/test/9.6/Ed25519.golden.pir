(letrec
    data (List :: * -> *) a | List_match where
      Nil : List a
      Cons : a -> List a -> List a
  in
  letrec
    !goList : List integer -> list integer
      = \(ds : List integer) ->
          List_match
            {integer}
            ds
            {list integer}
            []
            (\(d : integer) (ds : List integer) ->
               mkCons {integer} d (goList ds))
  in
  letrec
    !goList : List integer -> list integer
      = \(ds : List integer) ->
          List_match
            {integer}
            ds
            {list integer}
            []
            (\(d : integer) (ds : List integer) ->
               mkCons {integer} d (goList ds))
  in
  let
    !checkValid_f : bytestring -> integer = byteStringToInteger False
    data (Tuple2 :: * -> * -> *) a b | Tuple2_match where
      Tuple2 : a -> b -> Tuple2 a b
  in
  letrec
    !expModManual : integer -> integer -> integer -> integer
      = \(b' : integer) (e : integer) (m : integer) ->
          case
            (all dead. integer)
            (equalsInteger 0 e)
            [ (/\dead ->
                 let
                   !reduced : integer = expModManual b' (divideInteger e 2) m
                   !t : integer = modInteger (multiplyInteger reduced reduced) m
                 in
                 case
                   (all dead. integer)
                   (equalsInteger 0 (modInteger e 2))
                   [ (/\dead -> modInteger (multiplyInteger t b') m)
                   , (/\dead -> t) ]
                   {all dead. dead})
            , (/\dead -> 1) ]
            {all dead. dead}
  in
  let
    ~d :
       integer
      = multiplyInteger
          -121665
          (expModManual
             121666
             57896044618658097711785492504343953926634992332820282019728792003956564819947
             57896044618658097711785492504343953926634992332820282019728792003956564819949)
    !xRecover :
       integer -> integer
      = \(y : integer) ->
          let
            !i :
               integer
              = expModManual
                  2
                  14474011154664524427946373126085988481658748083205070504932198000989141204987
                  57896044618658097711785492504343953926634992332820282019728792003956564819949
            !xx :
               integer
              = multiplyInteger
                  (subtractInteger (multiplyInteger y y) 1)
                  (expModManual
                     (addInteger 1 (multiplyInteger (multiplyInteger d y) y))
                     57896044618658097711785492504343953926634992332820282019728792003956564819947
                     57896044618658097711785492504343953926634992332820282019728792003956564819949)
            !x :
               integer
              = expModManual
                  xx
                  7237005577332262213973186563042994240829374041602535252466099000494570602494
                  57896044618658097711785492504343953926634992332820282019728792003956564819949
            !xA :
               integer
              = multiplyInteger
                  x
                  (modInteger
                     i
                     57896044618658097711785492504343953926634992332820282019728792003956564819949)
            !xAB :
               integer
              = subtractInteger
                  57896044618658097711785492504343953926634992332820282019728792003956564819949
                  xA
            !xB :
               integer
              = subtractInteger
                  57896044618658097711785492504343953926634992332820282019728792003956564819949
                  x
            !`$j` : bool -> integer
              = \(cond : bool) ->
                  let
                    !`$j` : bool -> integer
                      = \(cond : bool) ->
                          case
                            (all dead. integer)
                            (case
                               (all dead. bool)
                               cond
                               [ (/\dead -> False)
                               , (/\dead -> case bool cond [True, False]) ]
                               {all dead. dead})
                            [ (/\dead ->
                                 case
                                   (all dead. integer)
                                   (case
                                      (all dead. bool)
                                      cond
                                      [(/\dead -> False), (/\dead -> cond)]
                                      {all dead. dead})
                                   [ (/\dead ->
                                        case
                                          (all dead. integer)
                                          (case
                                             (all dead. bool)
                                             (case bool cond [True, False])
                                             [ (/\dead -> False)
                                             , (/\dead -> cond) ]
                                             {all dead. dead})
                                          [(/\dead -> x), (/\dead -> xB)]
                                          {all dead. dead})
                                   , (/\dead -> xAB) ]
                                   {all dead. dead})
                            , (/\dead -> xA) ]
                            {all dead. dead}
                  in
                  case
                    (all dead. integer)
                    cond
                    [ (/\dead ->
                         case
                           (all dead. integer)
                           (equalsInteger 0 (modInteger x 2))
                           [(/\dead -> `$j` True), (/\dead -> `$j` False)]
                           {all dead. dead})
                    , (/\dead ->
                         case
                           (all dead. integer)
                           (equalsInteger 0 (modInteger xA 2))
                           [(/\dead -> `$j` True), (/\dead -> `$j` False)]
                           {all dead. dead}) ]
                    {all dead. dead}
          in
          case
            (all dead. integer)
            (equalsInteger
               0
               (modInteger
                  (subtractInteger (multiplyInteger x x) xx)
                  57896044618658097711785492504343953926634992332820282019728792003956564819949))
            [(/\dead -> `$j` True), (/\dead -> `$j` False)]
            {all dead. dead}
    !decodePoint :
       bytestring -> Tuple2 integer integer
      = \(bs : bytestring) ->
          let
            !yInt : integer
              = checkValid_f
                  (let
                    !ixes : List integer
                      = (let
                            a = List integer
                          in
                          \(c : integer -> a -> a) (n : a) -> c 7 n)
                          (\(ds : integer) (ds : List integer) ->
                             Cons {integer} ds ds)
                          (Nil {integer})
                  in
                  writeBits bs (goList ixes) False)
            !x : integer = xRecover yInt
            !x_ : bool = readBit bs 7
          in
          case
            (all dead. Tuple2 integer integer)
            (equalsInteger 0 (modInteger x 2))
            [ (/\dead ->
                 case
                   (all dead. Tuple2 integer integer)
                   x_
                   [ (/\dead ->
                        Tuple2
                          {integer}
                          {integer}
                          (subtractInteger
                             57896044618658097711785492504343953926634992332820282019728792003956564819949
                             x)
                          yInt)
                   , (/\dead -> Tuple2 {integer} {integer} x yInt) ]
                   {all dead. dead})
            , (/\dead ->
                 case
                   (all dead. Tuple2 integer integer)
                   x_
                   [ (/\dead -> Tuple2 {integer} {integer} x yInt)
                   , (/\dead ->
                        Tuple2
                          {integer}
                          {integer}
                          (subtractInteger
                             57896044618658097711785492504343953926634992332820282019728792003956564819949
                             x)
                          yInt) ]
                   {all dead. dead}) ]
            {all dead. dead}
    data SHA512Sched | SHA512Sched_match where
      SHA512Sched :
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        SHA512Sched
    !lsig512_ : bytestring -> bytestring
      = \(x : bytestring) ->
          xorByteString
            True
            (xorByteString True (rotateByteString x -1) (rotateByteString x -8))
            (shiftByteString x -7)
    !lsig512_ : bytestring -> bytestring
      = \(x : bytestring) ->
          xorByteString
            True
            (xorByteString
               True
               (rotateByteString x -19)
               (rotateByteString x -61))
            (shiftByteString x -6)
    !next : bytestring -> Tuple2 bytestring bytestring
      = \(bs : bytestring) ->
          let
            !len : integer = lengthOfByteString bs
          in
          Tuple2
            {bytestring}
            {bytestring}
            (sliceByteString 0 8 bs)
            (sliceByteString 8 len bs)
    data SHA512State | SHA512State_match where
      SHA512State :
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        bytestring ->
        SHA512State
  in
  letrec
    !runSha :
       SHA512State ->
       (bytestring -> SHA512State -> Tuple2 SHA512State bytestring) ->
       bytestring ->
       SHA512State
      = \(state : SHA512State)
         (next : bytestring -> SHA512State -> Tuple2 SHA512State bytestring)
         (input : bytestring) ->
          case
            (all dead. SHA512State)
            (equalsInteger 0 (lengthOfByteString input))
            [ (/\dead ->
                 Tuple2_match
                   {SHA512State}
                   {bytestring}
                   (next input state)
                   {SHA512State}
                   (\(ipv : SHA512State) (ipv : bytestring) ->
                      runSha ipv next ipv))
            , (/\dead -> state) ]
            {all dead. dead}
  in
  let
    !edwards :
       Tuple2 integer integer ->
       Tuple2 integer integer ->
       Tuple2 integer integer
      = \(ds : Tuple2 integer integer)
         (ds : Tuple2 integer integer) ->
          Tuple2_match
            {integer}
            {integer}
            ds
            {Tuple2 integer integer}
            (\(x : integer)
              (y : integer) ->
               Tuple2_match
                 {integer}
                 {integer}
                 ds
                 {Tuple2 integer integer}
                 (\(x : integer)
                   (y : integer) ->
                    let
                      !y :
                         integer
                        = multiplyInteger
                            (addInteger
                               (multiplyInteger y y)
                               (multiplyInteger x x))
                            (expModManual
                               (subtractInteger
                                  1
                                  (multiplyInteger
                                     (multiplyInteger
                                        (multiplyInteger
                                           (multiplyInteger d x)
                                           x)
                                        y)
                                     y))
                               57896044618658097711785492504343953926634992332820282019728792003956564819947
                               57896044618658097711785492504343953926634992332820282019728792003956564819949)
                    in
                    Tuple2
                      {integer}
                      {integer}
                      (modInteger
                         (multiplyInteger
                            (addInteger
                               (multiplyInteger x y)
                               (multiplyInteger x y))
                            (expModManual
                               (addInteger
                                  1
                                  (multiplyInteger
                                     (multiplyInteger
                                        (multiplyInteger
                                           (multiplyInteger d x)
                                           x)
                                        y)
                                     y))
                               57896044618658097711785492504343953926634992332820282019728792003956564819947
                               57896044618658097711785492504343953926634992332820282019728792003956564819949))
                         57896044618658097711785492504343953926634992332820282019728792003956564819949)
                      (modInteger
                         y
                         57896044618658097711785492504343953926634992332820282019728792003956564819949)))
  in
  letrec
    !scalarMult : Tuple2 integer integer -> integer -> Tuple2 integer integer
      = \(p : Tuple2 integer integer) (e : integer) ->
          case
            (all dead. Tuple2 integer integer)
            (equalsInteger 0 e)
            [ (/\dead ->
                 let
                   !nt : Tuple2 integer integer
                     = scalarMult p (divideInteger e 2)
                   !nt : Tuple2 integer integer = edwards nt nt
                 in
                 case
                   (all dead. Tuple2 integer integer)
                   (equalsInteger 0 (modInteger e 2))
                   [(/\dead -> edwards nt p), (/\dead -> nt)]
                   {all dead. dead})
            , (/\dead -> Tuple2 {integer} {integer} 0 1) ]
            {all dead. dead}
  in
  let
    !g : integer -> bytestring = integerToByteString True 8
    !`#+` : bytestring -> bytestring -> bytestring
      = \(x : bytestring) (y : bytestring) ->
          let
            !yI : integer = byteStringToInteger True y
            !added : integer = addInteger (byteStringToInteger True x) yI
          in
          case
            (all dead. bytestring)
            (lessThanInteger 18446744073709551615 added)
            [ (/\dead -> g added)
            , (/\dead ->
                 g
                   (subtractInteger
                      (subtractInteger added 18446744073709551615)
                      1)) ]
            {all dead. dead}
    !step : SHA512State -> integer -> bytestring -> SHA512State
      = \(ds : SHA512State) (k : integer) (w : bytestring) ->
          SHA512State_match
            ds
            {SHA512State}
            (\(x : bytestring)
              (x : bytestring)
              (x : bytestring)
              (x : bytestring)
              (x : bytestring)
              (x : bytestring)
              (x : bytestring)
              (x : bytestring) ->
               let
                 !nt : bytestring
                   = `#+`
                       (xorByteString
                          True
                          (xorByteString
                             True
                             (rotateByteString x -28)
                             (rotateByteString x -34))
                          (rotateByteString x -39))
                       (orByteString
                          True
                          (andByteString True x (orByteString True x x))
                          (andByteString True x x))
                 !nt : bytestring = integerToByteString True 8 k
                 !nt : bytestring
                   = `#+`
                       (`#+`
                          (`#+`
                             (`#+`
                                x
                                (xorByteString
                                   True
                                   (xorByteString
                                      True
                                      (rotateByteString x -14)
                                      (rotateByteString x -18))
                                   (rotateByteString x -41)))
                             (xorByteString
                                True
                                (andByteString True x x)
                                (andByteString
                                   True
                                   (complementByteString x)
                                   x)))
                          nt)
                       w
               in
               SHA512State (`#+` nt nt) x x x (`#+` x nt) x x x)
  in
  \(signature : data)
   (msg : data)
   (pk : data) ->
    let
      !sig : bytestring = unBData signature
      !message : bytestring = unBData msg
      !pubKey : bytestring = unBData pk
      !by :
         integer
        = multiplyInteger
            4
            (expModManual
               5
               57896044618658097711785492504343953926634992332820282019728792003956564819947
               57896044618658097711785492504343953926634992332820282019728792003956564819949)
      !bx : integer = xRecover by
      !s : integer = checkValid_f (sliceByteString 32 32 sig)
      !nt : Tuple2 integer integer = decodePoint pubKey
      !nt : Tuple2 integer integer = decodePoint (sliceByteString 0 32 sig)
      !h :
         integer
        = let
          !eta : bytestring
            = appendByteString
                (Tuple2_match
                   {integer}
                   {integer}
                   nt
                   {bytestring}
                   (\(x : integer) (y : integer) ->
                      let
                        !xLSBVal : bool
                          = readBit (integerToByteString False 32 x) 248
                        !yBS : bytestring = integerToByteString False 32 y
                        !ixes : List integer
                          = (let
                                a = List integer
                              in
                              \(c : integer -> a -> a) (n : a) -> c 7 n)
                              (\(ds : integer) (ds : List integer) ->
                                 Cons {integer} ds ds)
                              (Nil {integer})
                      in
                      writeBits yBS (goList ixes) xLSBVal))
                (appendByteString pubKey message)
        in
        byteStringToInteger
          False
          (SHA512State_match
             (runSha
                (SHA512State
                   #6a09e667f3bcc908
                   #bb67ae8584caa73b
                   #3c6ef372fe94f82b
                   #a54ff53a5f1d36f1
                   #510e527fade682d1
                   #9b05688c2b3e6c1f
                   #1f83d9abfb41bd6b
                   #5be0cd19137e2179)
                (\(bs : bytestring)
                  (s : SHA512State) ->
                   SHA512State_match
                     s
                     {Tuple2 SHA512State bytestring}
                     (\(a : bytestring)
                       (b : bytestring)
                       (c : bytestring)
                       (d : bytestring)
                       (e : bytestring)
                       (f : bytestring)
                       (g : bytestring)
                       (h : bytestring) ->
                        Tuple2_match
                          {SHA512Sched}
                          {bytestring}
                          (let
                            !ds : Tuple2 bytestring bytestring = next bs
                            ~w : bytestring
                              = Tuple2_match
                                  {bytestring}
                                  {bytestring}
                                  ds
                                  {bytestring}
                                  (\(w : bytestring) (rest : bytestring) -> w)
                          in
                          Tuple2_match
                            {bytestring}
                            {bytestring}
                            ds
                            {Tuple2 SHA512Sched bytestring}
                            (\(ipv : bytestring)
                              (ipv : bytestring) ->
                               let
                                 !ds : Tuple2 bytestring bytestring = next ipv
                                 ~w : bytestring
                                   = Tuple2_match
                                       {bytestring}
                                       {bytestring}
                                       ds
                                       {bytestring}
                                       (\(w : bytestring) (rest : bytestring) ->
                                          w)
                               in
                               Tuple2_match
                                 {bytestring}
                                 {bytestring}
                                 ds
                                 {Tuple2 SHA512Sched bytestring}
                                 (\(ipv : bytestring)
                                   (ipv : bytestring) ->
                                    let
                                      !ds : Tuple2 bytestring bytestring
                                        = next ipv
                                      ~w : bytestring
                                        = Tuple2_match
                                            {bytestring}
                                            {bytestring}
                                            ds
                                            {bytestring}
                                            (\(w : bytestring)
                                              (rest : bytestring) ->
                                               w)
                                    in
                                    Tuple2_match
                                      {bytestring}
                                      {bytestring}
                                      ds
                                      {Tuple2 SHA512Sched bytestring}
                                      (\(ipv : bytestring)
                                        (ipv : bytestring) ->
                                         let
                                           !ds : Tuple2 bytestring bytestring
                                             = next ipv
                                           ~w : bytestring
                                             = Tuple2_match
                                                 {bytestring}
                                                 {bytestring}
                                                 ds
                                                 {bytestring}
                                                 (\(w : bytestring)
                                                   (rest : bytestring) ->
                                                    w)
                                         in
                                         Tuple2_match
                                           {bytestring}
                                           {bytestring}
                                           ds
                                           {Tuple2 SHA512Sched bytestring}
                                           (\(ipv : bytestring)
                                             (ipv : bytestring) ->
                                              let
                                                !ds :
                                                   Tuple2 bytestring bytestring
                                                  = next ipv
                                                ~w : bytestring
                                                  = Tuple2_match
                                                      {bytestring}
                                                      {bytestring}
                                                      ds
                                                      {bytestring}
                                                      (\(w : bytestring)
                                                        (rest : bytestring) ->
                                                         w)
                                              in
                                              Tuple2_match
                                                {bytestring}
                                                {bytestring}
                                                ds
                                                {Tuple2 SHA512Sched bytestring}
                                                (\(ipv : bytestring)
                                                  (ipv : bytestring) ->
                                                   let
                                                     !ds :
                                                        Tuple2
                                                          bytestring
                                                          bytestring
                                                       = next ipv
                                                     ~w : bytestring
                                                       = Tuple2_match
                                                           {bytestring}
                                                           {bytestring}
                                                           ds
                                                           {bytestring}
                                                           (\(w : bytestring)
                                                             (rest :
                                                                bytestring) ->
                                                              w)
                                                   in
                                                   Tuple2_match
                                                     {bytestring}
                                                     {bytestring}
                                                     ds
                                                     {Tuple2
                                                        SHA512Sched
                                                        bytestring}
                                                     (\(ipv : bytestring)
                                                       (ipv : bytestring) ->
                                                        let
                                                          !ds :
                                                             Tuple2
                                                               bytestring
                                                               bytestring
                                                            = next ipv
                                                          ~w :
                                                             bytestring
                                                            = Tuple2_match
                                                                {bytestring}
                                                                {bytestring}
                                                                ds
                                                                {bytestring}
                                                                (\(w :
                                                                     bytestring)
                                                                  (rest :
                                                                     bytestring) ->
                                                                   w)
                                                        in
                                                        Tuple2_match
                                                          {bytestring}
                                                          {bytestring}
                                                          ds
                                                          {Tuple2
                                                             SHA512Sched
                                                             bytestring}
                                                          (\(ipv : bytestring)
                                                            (ipv :
                                                               bytestring) ->
                                                             let
                                                               !ds :
                                                                  Tuple2
                                                                    bytestring
                                                                    bytestring
                                                                 = next ipv
                                                               ~w :
                                                                  bytestring
                                                                 = Tuple2_match
                                                                     {bytestring}
                                                                     {bytestring}
                                                                     ds
                                                                     {bytestring}
                                                                     (\(w :
                                                                          bytestring)
                                                                       (rest :
                                                                          bytestring) ->
                                                                        w)
                                                             in
                                                             Tuple2_match
                                                               {bytestring}
                                                               {bytestring}
                                                               ds
                                                               {Tuple2
                                                                  SHA512Sched
                                                                  bytestring}
                                                               (\(ipv :
                                                                    bytestring)
                                                                 (ipv :
                                                                    bytestring) ->
                                                                  let
                                                                    !ds :
                                                                       Tuple2
                                                                         bytestring
                                                                         bytestring
                                                                      = next ipv
                                                                    ~w :
                                                                       bytestring
                                                                      = Tuple2_match
                                                                          {bytestring}
                                                                          {bytestring}
                                                                          ds
                                                                          {bytestring}
                                                                          (\(w :
                                                                               bytestring)
                                                                            (rest :
                                                                               bytestring) ->
                                                                             w)
                                                                  in
                                                                  Tuple2_match
                                                                    {bytestring}
                                                                    {bytestring}
                                                                    ds
                                                                    {Tuple2
                                                                       SHA512Sched
                                                                       bytestring}
                                                                    (\(ipv :
                                                                         bytestring)
                                                                      (ipv :
                                                                         bytestring) ->
                                                                       let
                                                                         !ds :
                                                                            Tuple2
                                                                              bytestring
                                                                              bytestring
                                                                           = next
                                                                               ipv
                                                                         ~w :
                                                                            bytestring
                                                                           = Tuple2_match
                                                                               {bytestring}
                                                                               {bytestring}
                                                                               ds
                                                                               {bytestring}
                                                                               (\(w :
                                                                                    bytestring)
                                                                                 (rest :
                                                                                    bytestring) ->
                                                                                  w)
                                                                       in
                                                                       Tuple2_match
                                                                         {bytestring}
                                                                         {bytestring}
                                                                         ds
                                                                         {Tuple2
                                                                            SHA512Sched
                                                                            bytestring}
                                                                         (\(ipv :
                                                                              bytestring)
                                                                           (ipv :
                                                                              bytestring) ->
                                                                            let
                                                                              !ds :
                                                                                 Tuple2
                                                                                   bytestring
                                                                                   bytestring
                                                                                = next
                                                                                    ipv
                                                                              ~w :
                                                                                 bytestring
                                                                                = Tuple2_match
                                                                                    {bytestring}
                                                                                    {bytestring}
                                                                                    ds
                                                                                    {bytestring}
                                                                                    (\(w :
                                                                                         bytestring)
                                                                                      (rest :
                                                                                         bytestring) ->
                                                                                       w)
                                                                            in
                                                                            Tuple2_match
                                                                              {bytestring}
                                                                              {bytestring}
                                                                              ds
                                                                              {Tuple2
                                                                                 SHA512Sched
                                                                                 bytestring}
                                                                              (\(ipv :
                                                                                   bytestring)
                                                                                (ipv :
                                                                                   bytestring) ->
                                                                                 let
                                                                                   !ds :
                                                                                      Tuple2
                                                                                        bytestring
                                                                                        bytestring
                                                                                     = next
                                                                                         ipv
                                                                                   ~w :
                                                                                      bytestring
                                                                                     = Tuple2_match
                                                                                         {bytestring}
                                                                                         {bytestring}
                                                                                         ds
                                                                                         {bytestring}
                                                                                         (\(w :
                                                                                              bytestring)
                                                                                           (rest :
                                                                                              bytestring) ->
                                                                                            w)
                                                                                 in
                                                                                 Tuple2_match
                                                                                   {bytestring}
                                                                                   {bytestring}
                                                                                   ds
                                                                                   {Tuple2
                                                                                      SHA512Sched
                                                                                      bytestring}
                                                                                   (\(ipv :
                                                                                        bytestring)
                                                                                     (ipv :
                                                                                        bytestring) ->
                                                                                      let
                                                                                        !ds :
                                                                                           Tuple2
                                                                                             bytestring
                                                                                             bytestring
                                                                                          = next
                                                                                              ipv
                                                                                        ~w :
                                                                                           bytestring
                                                                                          = Tuple2_match
                                                                                              {bytestring}
                                                                                              {bytestring}
                                                                                              ds
                                                                                              {bytestring}
                                                                                              (\(w :
                                                                                                   bytestring)
                                                                                                (rest :
                                                                                                   bytestring) ->
                                                                                                 w)
                                                                                      in
                                                                                      Tuple2_match
                                                                                        {bytestring}
                                                                                        {bytestring}
                                                                                        ds
                                                                                        {Tuple2
                                                                                           SHA512Sched
                                                                                           bytestring}
                                                                                        (\(ipv :
                                                                                             bytestring)
                                                                                          (ipv :
                                                                                             bytestring) ->
                                                                                           let
                                                                                             !ds :
                                                                                                Tuple2
                                                                                                  bytestring
                                                                                                  bytestring
                                                                                               = next
                                                                                                   ipv
                                                                                             ~w :
                                                                                                bytestring
                                                                                               = Tuple2_match
                                                                                                   {bytestring}
                                                                                                   {bytestring}
                                                                                                   ds
                                                                                                   {bytestring}
                                                                                                   (\(w :
                                                                                                        bytestring)
                                                                                                     (rest :
                                                                                                        bytestring) ->
                                                                                                      w)
                                                                                           in
                                                                                           Tuple2_match
                                                                                             {bytestring}
                                                                                             {bytestring}
                                                                                             ds
                                                                                             {Tuple2
                                                                                                SHA512Sched
                                                                                                bytestring}
                                                                                             (\(ipv :
                                                                                                  bytestring)
                                                                                               (ipv :
                                                                                                  bytestring) ->
                                                                                                let
                                                                                                  !ds :
                                                                                                     Tuple2
                                                                                                       bytestring
                                                                                                       bytestring
                                                                                                    = next
                                                                                                        ipv
                                                                                                  ~w :
                                                                                                     bytestring
                                                                                                    = Tuple2_match
                                                                                                        {bytestring}
                                                                                                        {bytestring}
                                                                                                        ds
                                                                                                        {bytestring}
                                                                                                        (\(w :
                                                                                                             bytestring)
                                                                                                          (rest :
                                                                                                             bytestring) ->
                                                                                                           w)
                                                                                                in
                                                                                                Tuple2_match
                                                                                                  {bytestring}
                                                                                                  {bytestring}
                                                                                                  ds
                                                                                                  {Tuple2
                                                                                                     SHA512Sched
                                                                                                     bytestring}
                                                                                                  (\(ipv :
                                                                                                       bytestring)
                                                                                                    (ipv :
                                                                                                       bytestring) ->
                                                                                                     let
                                                                                                       !ds :
                                                                                                          Tuple2
                                                                                                            bytestring
                                                                                                            bytestring
                                                                                                         = next
                                                                                                             ipv
                                                                                                       ~w :
                                                                                                          bytestring
                                                                                                         = Tuple2_match
                                                                                                             {bytestring}
                                                                                                             {bytestring}
                                                                                                             ds
                                                                                                             {bytestring}
                                                                                                             (\(w :
                                                                                                                  bytestring)
                                                                                                               (cont :
                                                                                                                  bytestring) ->
                                                                                                                w)
                                                                                                     in
                                                                                                     Tuple2_match
                                                                                                       {bytestring}
                                                                                                       {bytestring}
                                                                                                       ds
                                                                                                       {Tuple2
                                                                                                          SHA512Sched
                                                                                                          bytestring}
                                                                                                       (\(ipv :
                                                                                                            bytestring)
                                                                                                         (ipv :
                                                                                                            bytestring) ->
                                                                                                          let
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           w)
                                                                                                                        w)
                                                                                                                     (lsig512_
                                                                                                                        w))
                                                                                                                  w
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        w)
                                                                                                                     (lsig512_
                                                                                                                        w))
                                                                                                                  w
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        w)
                                                                                                                     (lsig512_
                                                                                                                        w))
                                                                                                                  w
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           w)
                                                                                                                        w)
                                                                                                                     (lsig512_
                                                                                                                        w))
                                                                                                                  w
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        w)
                                                                                                                     (lsig512_
                                                                                                                        w))
                                                                                                                  w
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        w)
                                                                                                                     (lsig512_
                                                                                                                        w))
                                                                                                                  w
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        w)
                                                                                                                     (lsig512_
                                                                                                                        w))
                                                                                                                  w
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        w))
                                                                                                                  w
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        w))
                                                                                                                  w
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        w))
                                                                                                                  w
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        w))
                                                                                                                  w
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        w))
                                                                                                                  w
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        w))
                                                                                                                  w
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        w))
                                                                                                                  w
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        w))
                                                                                                                  w
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  w
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = `#+`
                                                                                                                  (`#+`
                                                                                                                     (`#+`
                                                                                                                        (lsig512_
                                                                                                                           nt)
                                                                                                                        nt)
                                                                                                                     (lsig512_
                                                                                                                        nt))
                                                                                                                  nt
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = w
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = w
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = w
                                                                                                            !nt :
                                                                                                               bytestring
                                                                                                              = w
                                                                                                          in
                                                                                                          Tuple2
                                                                                                            {SHA512Sched}
                                                                                                            {bytestring}
                                                                                                            (SHA512Sched
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               w
                                                                                                               w
                                                                                                               w
                                                                                                               w
                                                                                                               w
                                                                                                               w
                                                                                                               w
                                                                                                               w
                                                                                                               w
                                                                                                               w
                                                                                                               w
                                                                                                               w
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt
                                                                                                               nt)
                                                                                                            ipv)))))))))))))))))
                          {Tuple2 SHA512State bytestring}
                          (\(ds : SHA512Sched)
                            (cont : bytestring) ->
                             SHA512Sched_match
                               ds
                               {Tuple2 SHA512State bytestring}
                               (\(w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring)
                                 (w : bytestring) ->
                                  SHA512State_match
                                    (step
                                       (step
                                          (step
                                             (step
                                                (step
                                                   (step
                                                      (step
                                                         (step
                                                            (step
                                                               (step
                                                                  (step
                                                                     (step
                                                                        (step
                                                                           (step
                                                                              (step
                                                                                 (step
                                                                                    (step
                                                                                       (step
                                                                                          (step
                                                                                             (step
                                                                                                (step
                                                                                                   (step
                                                                                                      (step
                                                                                                         (step
                                                                                                            (step
                                                                                                               (step
                                                                                                                  (step
                                                                                                                     (step
                                                                                                                        (step
                                                                                                                           (step
                                                                                                                              (step
                                                                                                                                 (step
                                                                                                                                    (step
                                                                                                                                       (step
                                                                                                                                          (step
                                                                                                                                             (step
                                                                                                                                                (step
                                                                                                                                                   (step
                                                                                                                                                      (step
                                                                                                                                                         (step
                                                                                                                                                            (step
                                                                                                                                                               (step
                                                                                                                                                                  (step
                                                                                                                                                                     (step
                                                                                                                                                                        (step
                                                                                                                                                                           (step
                                                                                                                                                                              (step
                                                                                                                                                                                 (step
                                                                                                                                                                                    (step
                                                                                                                                                                                       (step
                                                                                                                                                                                          (step
                                                                                                                                                                                             (step
                                                                                                                                                                                                (step
                                                                                                                                                                                                   (step
                                                                                                                                                                                                      (step
                                                                                                                                                                                                         (step
                                                                                                                                                                                                            (step
                                                                                                                                                                                                               (step
                                                                                                                                                                                                                  (step
                                                                                                                                                                                                                     (step
                                                                                                                                                                                                                        (step
                                                                                                                                                                                                                           (step
                                                                                                                                                                                                                              (step
                                                                                                                                                                                                                                 (step
                                                                                                                                                                                                                                    (step
                                                                                                                                                                                                                                       (step
                                                                                                                                                                                                                                          (step
                                                                                                                                                                                                                                             (step
                                                                                                                                                                                                                                                (step
                                                                                                                                                                                                                                                   (step
                                                                                                                                                                                                                                                      (step
                                                                                                                                                                                                                                                         (step
                                                                                                                                                                                                                                                            (step
                                                                                                                                                                                                                                                               (step
                                                                                                                                                                                                                                                                  (step
                                                                                                                                                                                                                                                                     (step
                                                                                                                                                                                                                                                                        (step
                                                                                                                                                                                                                                                                           (step
                                                                                                                                                                                                                                                                              (step
                                                                                                                                                                                                                                                                                 (step
                                                                                                                                                                                                                                                                                    s
                                                                                                                                                                                                                                                                                    4794697086780616226
                                                                                                                                                                                                                                                                                    w)
                                                                                                                                                                                                                                                                                 8158064640168781261
                                                                                                                                                                                                                                                                                 w)
                                                                                                                                                                                                                                                                              13096744586834688815
                                                                                                                                                                                                                                                                              w)
                                                                                                                                                                                                                                                                           16840607885511220156
                                                                                                                                                                                                                                                                           w)
                                                                                                                                                                                                                                                                        4131703408338449720
                                                                                                                                                                                                                                                                        w)
                                                                                                                                                                                                                                                                     6480981068601479193
                                                                                                                                                                                                                                                                     w)
                                                                                                                                                                                                                                                                  10538285296894168987
                                                                                                                                                                                                                                                                  w)
                                                                                                                                                                                                                                                               12329834152419229976
                                                                                                                                                                                                                                                               w)
                                                                                                                                                                                                                                                            15566598209576043074
                                                                                                                                                                                                                                                            w)
                                                                                                                                                                                                                                                         1334009975649890238
                                                                                                                                                                                                                                                         w)
                                                                                                                                                                                                                                                      2608012711638119052
                                                                                                                                                                                                                                                      w)
                                                                                                                                                                                                                                                   6128411473006802146
                                                                                                                                                                                                                                                   w)
                                                                                                                                                                                                                                                8268148722764581231
                                                                                                                                                                                                                                                w)
                                                                                                                                                                                                                                             9286055187155687089
                                                                                                                                                                                                                                             w)
                                                                                                                                                                                                                                          11230858885718282805
                                                                                                                                                                                                                                          w)
                                                                                                                                                                                                                                       13951009754708518548
                                                                                                                                                                                                                                       w)
                                                                                                                                                                                                                                    16472876342353939154
                                                                                                                                                                                                                                    w)
                                                                                                                                                                                                                                 17275323862435702243
                                                                                                                                                                                                                                 w)
                                                                                                                                                                                                                              1135362057144423861
                                                                                                                                                                                                                              w)
                                                                                                                                                                                                                           2597628984639134821
                                                                                                                                                                                                                           w)
                                                                                                                                                                                                                        3308224258029322869
                                                                                                                                                                                                                        w)
                                                                                                                                                                                                                     5365058923640841347
                                                                                                                                                                                                                     w)
                                                                                                                                                                                                                  6679025012923562964
                                                                                                                                                                                                                  w)
                                                                                                                                                                                                               8573033837759648693
                                                                                                                                                                                                               w)
                                                                                                                                                                                                            10970295158949994411
                                                                                                                                                                                                            w)
                                                                                                                                                                                                         12119686244451234320
                                                                                                                                                                                                         w)
                                                                                                                                                                                                      12683024718118986047
                                                                                                                                                                                                      w)
                                                                                                                                                                                                   13788192230050041572
                                                                                                                                                                                                   w)
                                                                                                                                                                                                14330467153632333762
                                                                                                                                                                                                w)
                                                                                                                                                                                             15395433587784984357
                                                                                                                                                                                             w)
                                                                                                                                                                                          489312712824947311
                                                                                                                                                                                          w)
                                                                                                                                                                                       1452737877330783856
                                                                                                                                                                                       w)
                                                                                                                                                                                    2861767655752347644
                                                                                                                                                                                    w)
                                                                                                                                                                                 3322285676063803686
                                                                                                                                                                                 w)
                                                                                                                                                                              5560940570517711597
                                                                                                                                                                              w)
                                                                                                                                                                           5996557281743188959
                                                                                                                                                                           w)
                                                                                                                                                                        7280758554555802590
                                                                                                                                                                        w)
                                                                                                                                                                     8532644243296465576
                                                                                                                                                                     w)
                                                                                                                                                                  9350256976987008742
                                                                                                                                                                  w)
                                                                                                                                                               10552545826968843579
                                                                                                                                                               w)
                                                                                                                                                            11727347734174303076
                                                                                                                                                            w)
                                                                                                                                                         12113106623233404929
                                                                                                                                                         w)
                                                                                                                                                      14000437183269869457
                                                                                                                                                      w)
                                                                                                                                                   14369950271660146224
                                                                                                                                                   w)
                                                                                                                                                15101387698204529176
                                                                                                                                                w)
                                                                                                                                             15463397548674623760
                                                                                                                                             w)
                                                                                                                                          17586052441742319658
                                                                                                                                          w)
                                                                                                                                       1182934255886127544
                                                                                                                                       w)
                                                                                                                                    1847814050463011016
                                                                                                                                    w)
                                                                                                                                 2177327727835720531
                                                                                                                                 w)
                                                                                                                              2830643537854262169
                                                                                                                              w)
                                                                                                                           3796741975233480872
                                                                                                                           w)
                                                                                                                        4115178125766777443
                                                                                                                        w)
                                                                                                                     5681478168544905931
                                                                                                                     w)
                                                                                                                  6601373596472566643
                                                                                                                  w)
                                                                                                               7507060721942968483
                                                                                                               w)
                                                                                                            8399075790359081724
                                                                                                            w)
                                                                                                         8693463985226723168
                                                                                                         w)
                                                                                                      9568029438360202098
                                                                                                      w)
                                                                                                   10144078919501101548
                                                                                                   w)
                                                                                                10430055236837252648
                                                                                                w)
                                                                                             11840083180663258601
                                                                                             w)
                                                                                          13761210420658862357
                                                                                          w)
                                                                                       14299343276471374635
                                                                                       w)
                                                                                    14566680578165727644
                                                                                    w)
                                                                                 15097957966210449927
                                                                                 w)
                                                                              16922976911328602910
                                                                              w)
                                                                           17689382322260857208
                                                                           w)
                                                                        500013540394364858
                                                                        w)
                                                                     748580250866718886
                                                                     w)
                                                                  1242879168328830382
                                                                  w)
                                                               1977374033974150939
                                                               w)
                                                            2944078676154940804
                                                            w)
                                                         3659926193048069267
                                                         w)
                                                      4368137639120453308
                                                      w)
                                                   4836135668995329356
                                                   w)
                                                5532061633213252278
                                                w)
                                             6448918945643986474
                                             w)
                                          6902733635092675308
                                          w)
                                       7801388544844847127
                                       w)
                                    {Tuple2 SHA512State bytestring}
                                    (\(ipv : bytestring)
                                      (ipv : bytestring)
                                      (ipv : bytestring)
                                      (ipv : bytestring)
                                      (ipv : bytestring)
                                      (ipv : bytestring)
                                      (ipv : bytestring)
                                      (ipv : bytestring) ->
                                       Tuple2
                                         {SHA512State}
                                         {bytestring}
                                         (SHA512State
                                            (`#+` a ipv)
                                            (`#+` b ipv)
                                            (`#+` c ipv)
                                            (`#+` d ipv)
                                            (`#+` e ipv)
                                            (`#+` f ipv)
                                            (`#+` g ipv)
                                            (`#+` h ipv))
                                         cont)))))
                (let
                  !lenBits : integer
                    = multiplyInteger 8 (lengthOfByteString eta)
                  !`$j` : integer -> bytestring
                    = \(k : integer) ->
                        appendByteString
                          eta
                          (appendByteString
                             (consByteString
                                128
                                (replicateByte
                                   (subtractInteger
                                      (divideInteger (addInteger 1 k) 8)
                                      1)
                                   0))
                             (integerToByteString True 16 lenBits))
                  !r : integer
                    = subtractInteger
                        (subtractInteger 896 (modInteger lenBits 1024))
                        1
                in
                case
                  (all dead. bytestring)
                  (lessThanEqualsInteger r -1)
                  [(/\dead -> `$j` r), (/\dead -> `$j` (addInteger 1024 r))]
                  {all dead. dead}))
             {bytestring}
             (\(x : bytestring)
               (x : bytestring)
               (x : bytestring)
               (x : bytestring)
               (x : bytestring)
               (x : bytestring)
               (x : bytestring)
               (x : bytestring) ->
                appendByteString
                  x
                  (appendByteString
                     x
                     (appendByteString
                        x
                        (appendByteString
                           x
                           (appendByteString
                              x
                              (appendByteString x (appendByteString x x))))))))
    in
    Tuple2_match
      {integer}
      {integer}
      (scalarMult
         (Tuple2
            {integer}
            {integer}
            (modInteger
               bx
               57896044618658097711785492504343953926634992332820282019728792003956564819949)
            (modInteger
               by
               57896044618658097711785492504343953926634992332820282019728792003956564819949))
         s)
      {bool}
      (\(x : integer) (y : integer) ->
         Tuple2_match
           {integer}
           {integer}
           (edwards nt (scalarMult nt h))
           {bool}
           (\(x : integer) (y : integer) ->
              case
                (all dead. bool)
                (equalsInteger x x)
                [(/\dead -> False), (/\dead -> equalsInteger y y)]
                {all dead. dead})))
  (B #c080c2932178c2adc2a7c3917a6009c3b37cc383245824c3a9c2a6c3aac080c286c2986c14c3b334c39915c298c2b47b244dc3a352c396c39a25c3b1c29d050e0509c298c28cc2abc3b0c38866c2b8c285c38bc3a37ac2a3c080c2b9c29b59c28bc2b2c3b902)
  (B #68656c6c6f20776f726c64)
  (B #283ac3bfc3bbc281372d5e77c3bdc2910b681bc2ab72c2bdc39f2fc395517a62c3b9c2af247ac39371c38311c386)