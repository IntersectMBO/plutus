let
  ~unsafeFromBuiltinData : all a. (\a -> data -> a) a -> data -> a
    = /\a -> \(v : (\a -> data -> a) a) -> v
in
let
  !unsafeDataAsMap : data -> list (pair data data) = unMapData
in
let
  !unsafeDataAsList : data -> list data = unListData
in
let
  !unsafeDataAsI : data -> integer = unIData
in
let
  !unsafeDataAsConstr : data -> pair integer (list data) = unConstrData
in
let
  !unsafeDataAsB : data -> bytestring = unBData
in
let
  !unitval : unit = ()
in
let
  ~toBuiltinData : all a. (\a -> a -> data) a -> a -> data
    = /\a -> \(v : (\a -> a -> data) a) -> v
in
let
  !mkI : integer -> data = iData
in
letrec
  data (Maybe :: * -> *) a | Maybe_match where
    Just : a -> Maybe a
    Nothing : Maybe a
in
let
  ~fromBuiltinData : all a. (\a -> data -> Maybe a) a -> data -> Maybe a
    = /\a -> \(v : (\a -> data -> Maybe a) a) -> v
in
let
  !error : all a. unit -> a = /\a -> \(thunk : unit) -> error {a}
in
let
  !equalsInteger : integer -> integer -> bool = equalsInteger
in
let
  !chooseData : all a. data -> a -> a -> a -> a -> a -> a = chooseData
in
let
  !casePair : all a b r. pair a b -> (a -> b -> r) -> r
    = /\a b r ->
        \(p : pair a b) (f : a -> b -> r) ->
          f (fstPair {a} {b} p) (sndPair {a} {b} p)
in
letrec
  data SomeVeryLargeEnum | SomeVeryLargeEnum_match where
    E10Ten : SomeVeryLargeEnum
    E1One : SomeVeryLargeEnum
    E2Two : SomeVeryLargeEnum
    E3Three : SomeVeryLargeEnum
    E4Four : SomeVeryLargeEnum
    E5Five : SomeVeryLargeEnum
    E6Six : SomeVeryLargeEnum
    E7Seven : SomeVeryLargeEnum
    E8Eight : SomeVeryLargeEnum
    E9Nine : SomeVeryLargeEnum
in
letrec
  data Unit | Unit_match where
    Unit : Unit
in
let
  ~`$cunsafeFromBuiltinData` : data -> SomeVeryLargeEnum
    = \(input : data) ->
        let
          !input : data = input
        in
        let
          !decoded : integer = unsafeDataAsI input
        in
        ifThenElse
          {all dead. SomeVeryLargeEnum}
          (equalsInteger decoded 0)
          (/\dead -> E1One)
          (/\dead ->
             ifThenElse
               {all dead. SomeVeryLargeEnum}
               (equalsInteger decoded 1)
               (/\dead -> E2Two)
               (/\dead ->
                  ifThenElse
                    {all dead. SomeVeryLargeEnum}
                    (equalsInteger decoded 2)
                    (/\dead -> E3Three)
                    (/\dead ->
                       ifThenElse
                         {all dead. SomeVeryLargeEnum}
                         (equalsInteger decoded 3)
                         (/\dead -> E4Four)
                         (/\dead ->
                            ifThenElse
                              {all dead. SomeVeryLargeEnum}
                              (equalsInteger decoded 4)
                              (/\dead -> E5Five)
                              (/\dead ->
                                 ifThenElse
                                   {all dead. SomeVeryLargeEnum}
                                   (equalsInteger decoded 5)
                                   (/\dead -> E6Six)
                                   (/\dead ->
                                      ifThenElse
                                        {all dead. SomeVeryLargeEnum}
                                        (equalsInteger decoded 6)
                                        (/\dead -> E7Seven)
                                        (/\dead ->
                                           ifThenElse
                                             {all dead. SomeVeryLargeEnum}
                                             (equalsInteger decoded 7)
                                             (/\dead -> E8Eight)
                                             (/\dead ->
                                                ifThenElse
                                                  {all dead. SomeVeryLargeEnum}
                                                  (equalsInteger decoded 8)
                                                  (/\dead -> E9Nine)
                                                  (/\dead ->
                                                     ifThenElse
                                                       {all dead.
                                                          SomeVeryLargeEnum}
                                                       (equalsInteger decoded 9)
                                                       (/\dead -> E10Ten)
                                                       (/\dead ->
                                                          error
                                                            {SomeVeryLargeEnum}
                                                            unitval)
                                                       {all dead. dead})
                                                  {all dead. dead})
                                             {all dead. dead})
                                        {all dead. dead})
                                   {all dead. dead})
                              {all dead. dead})
                         {all dead. dead})
                    {all dead. dead})
               {all dead. dead})
          {all dead. dead}
in
let
  ~`$fUnsafeFromDataSomeVeryLargeEnum` : (\a -> data -> a) SomeVeryLargeEnum
    = `$cunsafeFromBuiltinData`
in
let
  ~`$ctoBuiltinData` : SomeVeryLargeEnum -> data
    = \(ds : SomeVeryLargeEnum) ->
        SomeVeryLargeEnum_match
          ds
          {all dead. data}
          (/\dead -> mkI 9)
          (/\dead -> mkI 0)
          (/\dead -> mkI 1)
          (/\dead -> mkI 2)
          (/\dead -> mkI 3)
          (/\dead -> mkI 4)
          (/\dead -> mkI 5)
          (/\dead -> mkI 6)
          (/\dead -> mkI 7)
          (/\dead -> mkI 8)
          {all dead. dead}
in
let
  ~`$fToDataSomeVeryLargeEnum` : (\a -> a -> data) SomeVeryLargeEnum
    = `$ctoBuiltinData`
in
let
  ~`$cfromBuiltinData` :
     data -> Maybe SomeVeryLargeEnum
    = \(input : data) ->
        let
          !input : data = input
        in
        chooseData
          {Unit -> Maybe SomeVeryLargeEnum}
          input
          (\(ds : Unit) ->
             casePair
               {integer}
               {list data}
               {Maybe SomeVeryLargeEnum}
               (unsafeDataAsConstr input)
               (\(l : integer) (r : list data) -> Nothing {SomeVeryLargeEnum}))
          (\(ds : Unit) ->
             let
               !ds : list (pair data data) = unsafeDataAsMap input
             in
             Nothing {SomeVeryLargeEnum})
          (\(ds : Unit) ->
             let
               !ds : list data = unsafeDataAsList input
             in
             Nothing {SomeVeryLargeEnum})
          (\(ds : Unit) ->
             let
               !decoded : integer = unsafeDataAsI input
             in
             ifThenElse
               {all dead. Maybe SomeVeryLargeEnum}
               (equalsInteger decoded 0)
               (/\dead -> Just {SomeVeryLargeEnum} E1One)
               (/\dead ->
                  ifThenElse
                    {all dead. Maybe SomeVeryLargeEnum}
                    (equalsInteger decoded 1)
                    (/\dead -> Just {SomeVeryLargeEnum} E2Two)
                    (/\dead ->
                       ifThenElse
                         {all dead. Maybe SomeVeryLargeEnum}
                         (equalsInteger decoded 2)
                         (/\dead -> Just {SomeVeryLargeEnum} E3Three)
                         (/\dead ->
                            ifThenElse
                              {all dead. Maybe SomeVeryLargeEnum}
                              (equalsInteger decoded 3)
                              (/\dead -> Just {SomeVeryLargeEnum} E4Four)
                              (/\dead ->
                                 ifThenElse
                                   {all dead. Maybe SomeVeryLargeEnum}
                                   (equalsInteger decoded 4)
                                   (/\dead -> Just {SomeVeryLargeEnum} E5Five)
                                   (/\dead ->
                                      ifThenElse
                                        {all dead. Maybe SomeVeryLargeEnum}
                                        (equalsInteger decoded 5)
                                        (/\dead ->
                                           Just {SomeVeryLargeEnum} E6Six)
                                        (/\dead ->
                                           ifThenElse
                                             {all dead. Maybe SomeVeryLargeEnum}
                                             (equalsInteger decoded 6)
                                             (/\dead ->
                                                Just
                                                  {SomeVeryLargeEnum}
                                                  E7Seven)
                                             (/\dead ->
                                                ifThenElse
                                                  {all dead.
                                                     Maybe SomeVeryLargeEnum}
                                                  (equalsInteger decoded 7)
                                                  (/\dead ->
                                                     Just
                                                       {SomeVeryLargeEnum}
                                                       E8Eight)
                                                  (/\dead ->
                                                     ifThenElse
                                                       {all dead.
                                                          Maybe
                                                            SomeVeryLargeEnum}
                                                       (equalsInteger decoded 8)
                                                       (/\dead ->
                                                          Just
                                                            {SomeVeryLargeEnum}
                                                            E9Nine)
                                                       (/\dead ->
                                                          ifThenElse
                                                            {all dead.
                                                               Maybe
                                                                 SomeVeryLargeEnum}
                                                            (equalsInteger
                                                               decoded
                                                               9)
                                                            (/\dead ->
                                                               Just
                                                                 {SomeVeryLargeEnum}
                                                                 E10Ten)
                                                            (/\dead ->
                                                               Nothing
                                                                 {SomeVeryLargeEnum})
                                                            {all dead. dead})
                                                       {all dead. dead})
                                                  {all dead. dead})
                                             {all dead. dead})
                                        {all dead. dead})
                                   {all dead. dead})
                              {all dead. dead})
                         {all dead. dead})
                    {all dead. dead})
               {all dead. dead})
          (\(ds : Unit) ->
             let
               !ds : bytestring = unsafeDataAsB input
             in
             Nothing {SomeVeryLargeEnum})
          Unit
in
let
  ~`$fFromDataSomeVeryLargeEnum` : (\a -> data -> Maybe a) SomeVeryLargeEnum
    = `$cfromBuiltinData`
in
fromBuiltinData
  {SomeVeryLargeEnum}
  `$fFromDataSomeVeryLargeEnum`
  (toBuiltinData
     {SomeVeryLargeEnum}
     `$fToDataSomeVeryLargeEnum`
     (unsafeFromBuiltinData
        {SomeVeryLargeEnum}
        `$fUnsafeFromDataSomeVeryLargeEnum`
        (toBuiltinData {SomeVeryLargeEnum} `$fToDataSomeVeryLargeEnum` E10Ten)))