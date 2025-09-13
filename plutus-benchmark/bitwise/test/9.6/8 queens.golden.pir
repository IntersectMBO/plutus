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
    data (Tuple2 :: * -> * -> *) a b | Tuple2_match where
      Tuple2 : a -> b -> Tuple2 a b
  in
  letrec
    !selectByteString : integer -> bytestring -> integer
      = \(which : integer) (bs : bytestring) ->
          case
            (all dead. integer)
            (lessThanEqualsInteger which 0)
            [ (/\dead ->
                 let
                   !i : integer = selectByteString (subtractInteger which 1) bs
                 in
                 case
                   (all dead. integer)
                   (equalsInteger -1 i)
                   [ (/\dead ->
                        addInteger
                          (addInteger 1 i)
                          (findFirstSetBit
                             (shiftByteString
                                bs
                                (subtractInteger 0 (addInteger 1 i)))))
                   , (/\dead -> -1) ]
                   {all dead. dead})
            , (/\dead -> findFirstSetBit bs) ]
            {all dead. dead}
  in
  \(dim : data) ->
    let
      !dim : integer = unIData dim
      !lastRow : integer = subtractInteger dim 1
    in
    letrec
      !go :
         integer ->
         integer ->
         bytestring ->
         bytestring ->
         bytestring ->
         bytestring ->
         List (Tuple2 integer integer)
        = \(selectIx : integer)
           (row : integer)
           (down : bytestring)
           (left : bytestring)
           (right : bytestring)
           (control : bytestring) ->
            case
              (all dead. List (Tuple2 integer integer))
              (equalsInteger selectIx dim)
              [ (/\dead ->
                   let
                     !available : integer = selectByteString selectIx control
                   in
                   case
                     (all dead. List (Tuple2 integer integer))
                     (equalsInteger -1 available)
                     [ (/\dead ->
                          case
                            (all dead. List (Tuple2 integer integer))
                            (equalsInteger row lastRow)
                            [ (/\dead ->
                                 let
                                   !newRow : integer = addInteger 1 row
                                   !newRight : bytestring
                                     = shiftByteString
                                         (let
                                           !ixes : List integer
                                             = (let
                                                   a = List integer
                                                 in
                                                 \(c : integer -> a -> a)
                                                  (n : a) ->
                                                   c available n)
                                                 (\(ds : integer)
                                                   (ds : List integer) ->
                                                    Cons {integer} ds ds)
                                                 (Nil {integer})
                                         in
                                         writeBits right (goList ixes) True)
                                         -1
                                   !newLeft : bytestring
                                     = shiftByteString
                                         (let
                                           !ixes : List integer
                                             = (let
                                                   a = List integer
                                                 in
                                                 \(c : integer -> a -> a)
                                                  (n : a) ->
                                                   c available n)
                                                 (\(ds : integer)
                                                   (ds : List integer) ->
                                                    Cons {integer} ds ds)
                                                 (Nil {integer})
                                         in
                                         writeBits left (goList ixes) True)
                                         1
                                   !ixes : List integer
                                     = (let
                                           a = List integer
                                         in
                                         \(c : integer -> a -> a) (n : a) ->
                                           c available n)
                                         (\(ds : integer) (ds : List integer) ->
                                            Cons {integer} ds ds)
                                         (Nil {integer})
                                   !newDown : bytestring
                                     = writeBits down (goList ixes) True
                                   !newControl : bytestring
                                     = complementByteString
                                         (orByteString
                                            False
                                            newDown
                                            (orByteString
                                               False
                                               newLeft
                                               newRight))
                                 in
                                 List_match
                                   {Tuple2 integer integer}
                                   (go
                                      0
                                      newRow
                                      newDown
                                      newLeft
                                      newRight
                                      newControl)
                                   {all dead. List (Tuple2 integer integer)}
                                   (/\dead ->
                                      go
                                        (addInteger 1 selectIx)
                                        row
                                        down
                                        left
                                        right
                                        control)
                                   (\(ipv : Tuple2 integer integer)
                                     (ipv : List (Tuple2 integer integer)) ->
                                      /\dead ->
                                        Cons
                                          {Tuple2 integer integer}
                                          (Tuple2
                                             {integer}
                                             {integer}
                                             row
                                             available)
                                          (go
                                             0
                                             newRow
                                             newDown
                                             newLeft
                                             newRight
                                             newControl))
                                   {all dead. dead})
                            , (/\dead ->
                                 (let
                                     a = Tuple2 integer integer
                                   in
                                   \(g : all b. (a -> b -> b) -> b -> b) ->
                                     g
                                       {List a}
                                       (\(ds : a) (ds : List a) ->
                                          Cons {a} ds ds)
                                       (Nil {a}))
                                   (/\a ->
                                      \(c : Tuple2 integer integer -> a -> a)
                                       (n : a) ->
                                        c
                                          (Tuple2
                                             {integer}
                                             {integer}
                                             row
                                             available)
                                          n)) ]
                            {all dead. dead})
                     , (/\dead -> Nil {Tuple2 integer integer}) ]
                     {all dead. dead})
              , (/\dead -> Nil {Tuple2 integer integer}) ]
              {all dead. dead}
    in
    let
      !bytesNeeded : integer = quotientInteger dim 8
    in
    case
      (all dead. List (Tuple2 integer integer))
      (lessThanInteger dim 8)
      [ (/\dead ->
           case
             (all dead. List (Tuple2 integer integer))
             (equalsInteger 0 (remainderInteger dim 8))
             [ (/\dead -> Nil {Tuple2 integer integer})
             , (/\dead ->
                  let
                    !right : bytestring = replicateByte bytesNeeded 0
                    !left : bytestring = replicateByte bytesNeeded 0
                    !down : bytestring = replicateByte bytesNeeded 0
                  in
                  go 0 0 down left right (replicateByte bytesNeeded 255)) ]
             {all dead. dead})
      , (/\dead -> Nil {Tuple2 integer integer}) ]
      {all dead. dead})
  (I 8)