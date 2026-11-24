(let
    data (Tuple :: * -> * -> *) a b | Tuple_match where
      Tuple2 : a -> b -> Tuple a b
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
  letrec
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
  let
    !writeBits : bytestring -> List integer -> bool -> bytestring
      = \(bs : bytestring) (ixes : List integer) (bit : bool) ->
          writeBits bs (goList ixes) bit
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
         List (Tuple integer integer)
        = \(selectIx : integer)
           (row : integer)
           (down : bytestring)
           (left : bytestring)
           (right : bytestring)
           (control : bytestring) ->
            case
              (all dead. List (Tuple integer integer))
              (equalsInteger selectIx dim)
              [ (/\dead ->
                   let
                     !available : integer = selectByteString selectIx control
                   in
                   case
                     (all dead. List (Tuple integer integer))
                     (equalsInteger -1 available)
                     [ (/\dead ->
                          case
                            (all dead. List (Tuple integer integer))
                            (equalsInteger row lastRow)
                            [ (/\dead ->
                                 let
                                   !newRow : integer = addInteger 1 row
                                   !newRight : bytestring
                                     = shiftByteString
                                         (writeBits
                                            right
                                            ((let
                                                 a = List integer
                                               in
                                               \(c : integer -> a -> a)
                                                (n : a) ->
                                                 c available n)
                                               (\(ds : integer)
                                                 (ds : List integer) ->
                                                  Cons {integer} ds ds)
                                               (Nil {integer}))
                                            True)
                                         -1
                                   !newLeft : bytestring
                                     = shiftByteString
                                         (writeBits
                                            left
                                            ((let
                                                 a = List integer
                                               in
                                               \(c : integer -> a -> a)
                                                (n : a) ->
                                                 c available n)
                                               (\(ds : integer)
                                                 (ds : List integer) ->
                                                  Cons {integer} ds ds)
                                               (Nil {integer}))
                                            True)
                                         1
                                   !newDown : bytestring
                                     = writeBits
                                         down
                                         ((let
                                              a = List integer
                                            in
                                            \(c : integer -> a -> a) (n : a) ->
                                              c available n)
                                            (\(ds : integer)
                                              (ds : List integer) ->
                                               Cons {integer} ds ds)
                                            (Nil {integer}))
                                         True
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
                                   {Tuple integer integer}
                                   (go
                                      0
                                      newRow
                                      newDown
                                      newLeft
                                      newRight
                                      newControl)
                                   {all dead. List (Tuple integer integer)}
                                   (/\dead ->
                                      go
                                        (addInteger 1 selectIx)
                                        row
                                        down
                                        left
                                        right
                                        control)
                                   (\(ipv : Tuple integer integer)
                                     (ipv : List (Tuple integer integer)) ->
                                      /\dead ->
                                        Cons
                                          {Tuple integer integer}
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
                                     a = Tuple integer integer
                                   in
                                   \(g : all b. (a -> b -> b) -> b -> b) ->
                                     g
                                       {List a}
                                       (\(ds : a) (ds : List a) ->
                                          Cons {a} ds ds)
                                       (Nil {a}))
                                   (/\a ->
                                      \(c : Tuple integer integer -> a -> a)
                                       (n : a) ->
                                        c
                                          (Tuple2
                                             {integer}
                                             {integer}
                                             row
                                             available)
                                          n)) ]
                            {all dead. dead})
                     , (/\dead -> Nil {Tuple integer integer}) ]
                     {all dead. dead})
              , (/\dead -> Nil {Tuple integer integer}) ]
              {all dead. dead}
    in
    let
      !bytesNeeded : integer = quotientInteger dim 8
    in
    case
      (all dead. List (Tuple integer integer))
      (lessThanInteger dim 8)
      [ (/\dead ->
           case
             (all dead. List (Tuple integer integer))
             (equalsInteger 0 (remainderInteger dim 8))
             [ (/\dead -> Nil {Tuple integer integer})
             , (/\dead ->
                  let
                    !right : bytestring = replicateByte bytesNeeded 0
                    !left : bytestring = replicateByte bytesNeeded 0
                    !down : bytestring = replicateByte bytesNeeded 0
                  in
                  go 0 0 down left right (replicateByte bytesNeeded 255)) ]
             {all dead. dead})
      , (/\dead -> Nil {Tuple integer integer}) ]
      {all dead. dead})
  (I 8)