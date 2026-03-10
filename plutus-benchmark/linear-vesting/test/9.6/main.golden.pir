(letrec
    !countInputsAtScript : bytestring -> list data -> integer
      = \(scriptHash : bytestring) (inputs : list data) ->
          case
            integer
            inputs
            [ (\(txIn : data) (txIns : list data) ->
                 let
                   !rest : integer = countInputsAtScript scriptHash txIns
                   !credCon : pair integer (list data)
                     = unConstrData
                         (headList
                            {data}
                            (case
                               (list data)
                               (unConstrData
                                  (headList
                                     {data}
                                     (case
                                        (list data)
                                        (unConstrData
                                           (headList
                                              {data}
                                              (tailList
                                                 {data}
                                                 (case
                                                    (list data)
                                                    (unConstrData txIn)
                                                    [ (\(l : integer)
                                                        (r : list data) ->
                                                         r) ]))))
                                        [ (\(l : integer) (r : list data) ->
                                             r) ])))
                               [(\(l : integer) (r : list data) -> r)]))
                   !credTag : integer
                     = case
                         integer
                         credCon
                         [(\(l : integer) (r : list data) -> l)]
                   !credFields : list data
                     = case
                         (list data)
                         credCon
                         [(\(l : integer) (r : list data) -> r)]
                 in
                 case
                   (all dead. integer)
                   (equalsInteger 1 credTag)
                   [ (/\dead -> rest)
                   , (/\dead ->
                        case
                          (all dead. integer)
                          (equalsByteString
                             (unBData (headList {data} credFields))
                             scriptHash)
                          [(/\dead -> rest), (/\dead -> addInteger 1 rest)]
                          {all dead. dead}) ]
                   {all dead. dead})
            , 0 ]
  in
  let
    data Unit | Unit_match where
      Unit : Unit
    !caseList' : all a r. r -> (a -> list a -> r) -> list a -> r
      = /\a r ->
          \(z : r) (f : a -> list a -> r) (xs : list a) -> case r xs [f, z]
  in
  letrec
    !findInputByOutRef : data -> list data -> data
      = \(ref : data) (inputs : list data) ->
          caseList'
            {data}
            {data}
            (let
              !x : Unit = trace {Unit} "Own input not found" Unit
            in
            error {data})
            (\(txIn : data) (txIns : list data) ->
               case
                 (all dead. data)
                 (equalsData
                    (headList
                       {data}
                       (case
                          (list data)
                          (unConstrData txIn)
                          [(\(l : integer) (r : list data) -> r)]))
                    ref)
                 [(/\dead -> findInputByOutRef ref txIns), (/\dead -> txIn)]
                 {all dead. dead})
            inputs
  in
  letrec
    !findOutputByAddress : data -> list data -> data
      = \(addr : data) (outputs : list data) ->
          caseList'
            {data}
            {data}
            (let
              !x : Unit = trace {Unit} "Own output not found" Unit
            in
            error {data})
            (\(out : data) (outs : list data) ->
               case
                 (all dead. data)
                 (equalsData
                    (headList
                       {data}
                       (case
                          (list data)
                          (unConstrData out)
                          [(\(l : integer) (r : list data) -> r)]))
                    addr)
                 [(/\dead -> findOutputByAddress addr outs), (/\dead -> out)]
                 {all dead. dead})
            outputs
  in
  letrec
    !txSignedBy' : list data -> bytestring -> bool
      = \(signatories : list data) (pkh : bytestring) ->
          case
            bool
            signatories
            [ (\(s : data) (ss : list data) ->
                 case
                   (all dead. bool)
                   (equalsByteString (unBData s) pkh)
                   [(/\dead -> txSignedBy' ss pkh), (/\dead -> True)]
                   {all dead. dead})
            , False ]
  in
  \(scriptContextData : data) ->
    let
      !ctxFields : list data
        = case
            (list data)
            (unConstrData
               (trace {data} "Parsing ScriptContext..." scriptContextData))
            [(\(l : integer) (r : list data) -> r)]
      !txInfoFields : list data
        = case
            (list data)
            (unConstrData (headList {data} ctxFields))
            [(\(l : integer) (r : list data) -> r)]
      !txInfoFields : list data = tailList {data} (tailList {data} txInfoFields)
      !txInfoFields : list data
        = tailList
            {data}
            (tailList
               {data}
               (tailList
                  {data}
                  (tailList {data} (tailList {data} txInfoFields))))
      !txSignatories : list data
        = unListData (headList {data} (tailList {data} txInfoFields))
      !txValidRange : data = headList {data} txInfoFields
      !txOutputs : list data = unListData (headList {data} txInfoFields)
      !txInputs : list data = unListData (headList {data} txInfoFields)
      !redeemerTag : integer
        = case
            integer
            (unConstrData (headList {data} (tailList {data} ctxFields)))
            [(\(l : integer) (r : list data) -> l)]
      !spendingInfo : pair data data
        = let
          !con : pair integer (list data)
            = unConstrData
                (headList {data} (tailList {data} (tailList {data} ctxFields)))
          !tag : integer
            = case integer con [(\(l : integer) (r : list data) -> l)]
          !fields : list data
            = case (list data) con [(\(l : integer) (r : list data) -> r)]
        in
        case
          (all dead. pair data data)
          (equalsInteger 1 tag)
          [ (/\dead ->
               let
                 !x : Unit = trace {Unit} "Not spending script" Unit
               in
               error {pair data data})
          , (/\dead ->
               let
                 !mdCon : pair integer (list data)
                   = unConstrData (headList {data} (tailList {data} fields))
                 !mdTag : integer
                   = case integer mdCon [(\(l : integer) (r : list data) -> l)]
                 !mdFields : list data
                   = case
                       (list data)
                       mdCon
                       [(\(l : integer) (r : list data) -> r)]
                 !ownRef : data = headList {data} fields
               in
               case
                 (all dead. pair data data)
                 (equalsInteger 0 mdTag)
                 [ (/\dead ->
                      let
                        !x : Unit = trace {Unit} "Missing datum" Unit
                      in
                      error {pair data data})
                 , (/\dead -> mkPairData ownRef (headList {data} mdFields)) ]
                 {all dead. dead}) ]
          {all dead. dead}
      !ownRef : data = case data spendingInfo [(\(l : data) (r : data) -> l)]
      !datumData : data = case data spendingInfo [(\(l : data) (r : data) -> r)]
    in
    case
      (all dead. unit)
      (trace
         {bool}
         "Parsed ScriptContext"
         (trace
            {bool}
            "Parsed Redeemer"
            (case
               bool
               redeemerTag
               [ (trace
                    {bool}
                    "Partial unlock requested"
                    (let
                      !currentTimeApproximation : integer
                        = let
                          !lowerFields : list data
                            = case
                                (list data)
                                (unConstrData
                                   (headList
                                      {data}
                                      (case
                                         (list data)
                                         (unConstrData txValidRange)
                                         [ (\(l : integer) (r : list data) ->
                                              r) ])))
                                [(\(l : integer) (r : list data) -> r)]
                          !extCon : pair integer (list data)
                            = unConstrData (headList {data} lowerFields)
                          !extTag : integer
                            = case
                                integer
                                extCon
                                [(\(l : integer) (r : list data) -> l)]
                          !extFields : list data
                            = case
                                (list data)
                                extCon
                                [(\(l : integer) (r : list data) -> r)]
                          !offset : integer
                            = case
                                integer
                                (equalsInteger
                                   1
                                   (case
                                      integer
                                      (unConstrData
                                         (headList
                                            {data}
                                            (tailList {data} lowerFields)))
                                      [(\(l : integer) (r : list data) -> l)]))
                                [1, 0]
                        in
                        case
                          (all dead. integer)
                          (equalsInteger 1 extTag)
                          [ (/\dead ->
                               let
                                 !x : Unit
                                   = trace {Unit} "Time range not Finite" Unit
                               in
                               error {integer})
                          , (/\dead ->
                               addInteger
                                 (unIData (headList {data} extFields))
                                 offset) ]
                          {all dead. dead}
                      !vdFields : list data
                        = case
                            (list data)
                            (unConstrData datumData)
                            [(\(l : integer) (r : list data) -> r)]
                      !vdFields : list data = tailList {data} vdFields
                      !vdFields : list data = tailList {data} vdFields
                      !vdFields : list data = tailList {data} vdFields
                      !vdFields : list data = tailList {data} vdFields
                      !vdFields : list data = tailList {data} vdFields
                      !totalInstallments : integer
                        = unIData (headList {data} (tailList {data} vdFields))
                      !firstUnlockPossibleAfter : integer
                        = unIData (headList {data} vdFields)
                      !vestingPeriodEnd : integer
                        = unIData (headList {data} vdFields)
                      !vestingTimeRemaining : integer
                        = subtractInteger
                            vestingPeriodEnd
                            currentTimeApproximation
                      !timeBetweenTwoInstallments : integer
                        = addInteger
                            1
                            (divideInteger
                               (subtractInteger
                                  (subtractInteger
                                     vestingPeriodEnd
                                     (unIData (headList {data} vdFields)))
                                  1)
                               totalInstallments)
                      !expectedRemainingQty : integer
                        = addInteger
                            1
                            (divideInteger
                               (subtractInteger
                                  (multiplyInteger
                                     (addInteger
                                        1
                                        (divideInteger
                                           (subtractInteger
                                              vestingTimeRemaining
                                              1)
                                           timeBetweenTwoInstallments))
                                     (unIData (headList {data} vdFields)))
                                  1)
                               totalInstallments)
                      !assetFields : list data
                        = case
                            (list data)
                            (unConstrData (headList {data} vdFields))
                            [(\(l : integer) (r : list data) -> r)]
                      !assetCs : bytestring
                        = unBData (headList {data} assetFields)
                      !assetTn : bytestring
                        = unBData
                            (headList {data} (tailList {data} assetFields))
                    in
                    letrec
                      !findToken : list (pair data data) -> integer
                        = \(pairs : list (pair data data)) ->
                            case
                              (all dead. integer)
                              (nullList {pair data data} pairs)
                              [ (/\dead ->
                                   let
                                     !pair : pair data data
                                       = headList {pair data data} pairs
                                   in
                                   case
                                     (all dead. integer)
                                     (equalsByteString
                                        (unBData
                                           (case
                                              data
                                              pair
                                              [(\(l : data) (r : data) -> l)]))
                                        assetTn)
                                     [ (/\dead ->
                                          findToken
                                            (tailList {pair data data} pairs))
                                     , (/\dead ->
                                          unIData
                                            (case
                                               data
                                               pair
                                               [ (\(l : data) (r : data) ->
                                                    r) ])) ]
                                     {all dead. dead})
                              , (/\dead -> 0) ]
                              {all dead. dead}
                    in
                    letrec
                      !findCurrency : list (pair data data) -> integer
                        = \(pairs : list (pair data data)) ->
                            case
                              (all dead. integer)
                              (nullList {pair data data} pairs)
                              [ (/\dead ->
                                   let
                                     !pair : pair data data
                                       = headList {pair data data} pairs
                                   in
                                   case
                                     (all dead. integer)
                                     (equalsByteString
                                        (unBData
                                           (case
                                              data
                                              pair
                                              [(\(l : data) (r : data) -> l)]))
                                        assetCs)
                                     [ (/\dead ->
                                          findCurrency
                                            (tailList {pair data data} pairs))
                                     , (/\dead ->
                                          findToken
                                            (unMapData
                                               (case
                                                  data
                                                  pair
                                                  [ (\(l : data) (r : data) ->
                                                       r) ]))) ]
                                     {all dead. dead})
                              , (/\dead -> 0) ]
                              {all dead. dead}
                    in
                    letrec
                      !findToken : list (pair data data) -> integer
                        = \(pairs : list (pair data data)) ->
                            case
                              (all dead. integer)
                              (nullList {pair data data} pairs)
                              [ (/\dead ->
                                   let
                                     !pair : pair data data
                                       = headList {pair data data} pairs
                                   in
                                   case
                                     (all dead. integer)
                                     (equalsByteString
                                        (unBData
                                           (case
                                              data
                                              pair
                                              [(\(l : data) (r : data) -> l)]))
                                        assetTn)
                                     [ (/\dead ->
                                          findToken
                                            (tailList {pair data data} pairs))
                                     , (/\dead ->
                                          unIData
                                            (case
                                               data
                                               pair
                                               [ (\(l : data) (r : data) ->
                                                    r) ])) ]
                                     {all dead. dead})
                              , (/\dead -> 0) ]
                              {all dead. dead}
                    in
                    letrec
                      !findCurrency : list (pair data data) -> integer
                        = \(pairs : list (pair data data)) ->
                            case
                              (all dead. integer)
                              (nullList {pair data data} pairs)
                              [ (/\dead ->
                                   let
                                     !pair : pair data data
                                       = headList {pair data data} pairs
                                   in
                                   case
                                     (all dead. integer)
                                     (equalsByteString
                                        (unBData
                                           (case
                                              data
                                              pair
                                              [(\(l : data) (r : data) -> l)]))
                                        assetCs)
                                     [ (/\dead ->
                                          findCurrency
                                            (tailList {pair data data} pairs))
                                     , (/\dead ->
                                          findToken
                                            (unMapData
                                               (case
                                                  data
                                                  pair
                                                  [ (\(l : data) (r : data) ->
                                                       r) ]))) ]
                                     {all dead. dead})
                              , (/\dead -> 0) ]
                              {all dead. dead}
                    in
                    let
                      !beneficiaryHash : bytestring
                        = unBData
                            (headList
                               {data}
                               (case
                                  (list data)
                                  (unConstrData
                                     (headList
                                        {data}
                                        (case
                                           (list data)
                                           (unConstrData
                                              (headList {data} vdFields))
                                           [ (\(l : integer) (r : list data) ->
                                                r) ])))
                                  [(\(l : integer) (r : list data) -> r)]))
                      !signed : bool = txSignedBy' txSignatories beneficiaryHash
                      !resolvedFields : list data
                        = case
                            (list data)
                            (unConstrData
                               (headList
                                  {data}
                                  (tailList
                                     {data}
                                     (case
                                        (list data)
                                        (unConstrData
                                           (findInputByOutRef ownRef txInputs))
                                        [ (\(l : integer) (r : list data) ->
                                             r) ]))))
                            [(\(l : integer) (r : list data) -> r)]
                      !inputAddress : data = headList {data} resolvedFields
                      !scriptHash : bytestring
                        = unBData
                            (headList
                               {data}
                               (case
                                  (list data)
                                  (unConstrData
                                     (headList
                                        {data}
                                        (case
                                           (list data)
                                           (unConstrData inputAddress)
                                           [ (\(l : integer) (r : list data) ->
                                                r) ])))
                                  [(\(l : integer) (r : list data) -> r)]))
                      !ownOutputFields : list data
                        = case
                            (list data)
                            (unConstrData
                               (findOutputByAddress inputAddress txOutputs))
                            [(\(l : integer) (r : list data) -> r)]
                      !outputDatum : data
                        = headList
                            {data}
                            (tailList {data} (tailList {data} ownOutputFields))
                      !newRemainingQty : integer
                        = let
                          !valueData : data
                            = headList {data} (tailList {data} ownOutputFields)
                        in
                        findCurrency (unMapData valueData)
                      !resolvedDatum : data
                        = headList
                            {data}
                            (tailList {data} (tailList {data} resolvedFields))
                      !oldRemainingQty : integer
                        = let
                          !valueData : data
                            = headList {data} (tailList {data} resolvedFields)
                        in
                        findCurrency (unMapData valueData)
                    in
                    case
                      (all dead. bool)
                      (case bool signed [True, False])
                      [ (/\dead ->
                           case
                             (all dead. bool)
                             (lessThanEqualsInteger
                                currentTimeApproximation
                                firstUnlockPossibleAfter)
                             [ (/\dead ->
                                  case
                                    (all dead. bool)
                                    (lessThanEqualsInteger newRemainingQty 0)
                                    [ (/\dead ->
                                         case
                                           (all dead. bool)
                                           (lessThanEqualsInteger
                                              oldRemainingQty
                                              newRemainingQty)
                                           [ (/\dead ->
                                                case
                                                  (all dead. bool)
                                                  (case
                                                     bool
                                                     (equalsInteger
                                                        expectedRemainingQty
                                                        newRemainingQty)
                                                     [True, False])
                                                  [ (/\dead ->
                                                       case
                                                         (all dead. bool)
                                                         (case
                                                            bool
                                                            (equalsData
                                                               resolvedDatum
                                                               outputDatum)
                                                            [True, False])
                                                         [ (/\dead ->
                                                              case
                                                                (all dead. bool)
                                                                (case
                                                                   bool
                                                                   (equalsInteger
                                                                      1
                                                                      (countInputsAtScript
                                                                         scriptHash
                                                                         txInputs))
                                                                   [ True
                                                                   , False ])
                                                                [ (/\dead ->
                                                                     True)
                                                                , (/\dead ->
                                                                     let
                                                                       !x :
                                                                          Unit
                                                                         = trace
                                                                             {Unit}
                                                                             "Double satisfaction"
                                                                             Unit
                                                                     in
                                                                     error
                                                                       {bool}) ]
                                                                {all dead.
                                                                   dead})
                                                         , (/\dead ->
                                                              let
                                                                !x :
                                                                   Unit
                                                                  = trace
                                                                      {Unit}
                                                                      "Datum Modification Prohibited"
                                                                      Unit
                                                              in
                                                              error {bool}) ]
                                                         {all dead. dead})
                                                  , (/\dead ->
                                                       let
                                                         !x :
                                                            Unit
                                                           = trace
                                                               {Unit}
                                                               "Mismatched remaining asset"
                                                               Unit
                                                       in
                                                       error {bool}) ]
                                                  {all dead. dead})
                                           , (/\dead ->
                                                let
                                                  !x :
                                                     Unit
                                                    = trace
                                                        {Unit}
                                                        "Remaining asset is not decreasing"
                                                        Unit
                                                in
                                                error {bool}) ]
                                           {all dead. dead})
                                    , (/\dead ->
                                         let
                                           !x :
                                              Unit
                                             = trace
                                                 {Unit}
                                                 "Zero remaining assets not allowed"
                                                 Unit
                                         in
                                         error {bool}) ]
                                    {all dead. dead})
                             , (/\dead ->
                                  let
                                    !x :
                                       Unit
                                      = trace
                                          {Unit}
                                          "Unlock not permitted until firstUnlockPossibleAfter time"
                                          Unit
                                  in
                                  error {bool}) ]
                             {all dead. dead})
                      , (/\dead ->
                           let
                             !x : Unit
                               = trace
                                   {Unit}
                                   "Missing beneficiary signature"
                                   Unit
                           in
                           error {bool}) ]
                      {all dead. dead}))
               , (trace
                    {bool}
                    "Full unlock requested"
                    (let
                      !currentTimeApproximation : integer
                        = let
                          !lowerFields : list data
                            = case
                                (list data)
                                (unConstrData
                                   (headList
                                      {data}
                                      (case
                                         (list data)
                                         (unConstrData txValidRange)
                                         [ (\(l : integer) (r : list data) ->
                                              r) ])))
                                [(\(l : integer) (r : list data) -> r)]
                          !extCon : pair integer (list data)
                            = unConstrData (headList {data} lowerFields)
                          !extTag : integer
                            = case
                                integer
                                extCon
                                [(\(l : integer) (r : list data) -> l)]
                          !extFields : list data
                            = case
                                (list data)
                                extCon
                                [(\(l : integer) (r : list data) -> r)]
                          !offset : integer
                            = case
                                integer
                                (equalsInteger
                                   1
                                   (case
                                      integer
                                      (unConstrData
                                         (headList
                                            {data}
                                            (tailList {data} lowerFields)))
                                      [(\(l : integer) (r : list data) -> l)]))
                                [1, 0]
                        in
                        case
                          (all dead. integer)
                          (equalsInteger 1 extTag)
                          [ (/\dead ->
                               let
                                 !x : Unit
                                   = trace {Unit} "Time range not Finite" Unit
                               in
                               error {integer})
                          , (/\dead ->
                               addInteger
                                 (unIData (headList {data} extFields))
                                 offset) ]
                          {all dead. dead}
                      !vdFields : list data
                        = case
                            (list data)
                            (unConstrData datumData)
                            [(\(l : integer) (r : list data) -> r)]
                      !vestingPeriodEnd : integer
                        = unIData
                            (headList
                               {data}
                               (tailList
                                  {data}
                                  (tailList
                                     {data}
                                     (tailList
                                        {data}
                                        (tailList {data} vdFields)))))
                      !beneficiaryHash : bytestring
                        = unBData
                            (headList
                               {data}
                               (case
                                  (list data)
                                  (unConstrData
                                     (headList
                                        {data}
                                        (case
                                           (list data)
                                           (unConstrData
                                              (headList {data} vdFields))
                                           [ (\(l : integer) (r : list data) ->
                                                r) ])))
                                  [(\(l : integer) (r : list data) -> r)]))
                    in
                    case
                      (all dead. bool)
                      (case
                         bool
                         (txSignedBy' txSignatories beneficiaryHash)
                         [True, False])
                      [ (/\dead ->
                           case
                             (all dead. bool)
                             (lessThanEqualsInteger
                                currentTimeApproximation
                                vestingPeriodEnd)
                             [ (/\dead -> True)
                             , (/\dead ->
                                  let
                                    !x :
                                       Unit
                                      = trace
                                          {Unit}
                                          "Unlock not permitted until vestingPeriodEnd time"
                                          Unit
                                  in
                                  error {bool}) ]
                             {all dead. dead})
                      , (/\dead ->
                           let
                             !x : Unit
                               = trace
                                   {Unit}
                                   "Missing beneficiary signature"
                                   Unit
                           in
                           error {bool}) ]
                      {all dead. dead})) ])))
      [ (/\dead ->
           let
             !x : Unit = trace {Unit} "Validation failed" Unit
           in
           error {unit})
      , (/\dead -> trace {unit} "Validation completed" ()) ]
      {all dead. dead})
  (Constr 0
     [ Constr 0
         [ List
             [ Constr 0
                 [ Constr 0
                     [ B #058fdca70be67c74151cea3846be7f73342d92c0090b62c1052e6790ad83f145
                     , I 0 ]
                 , Constr 0
                     [ Constr 0 [Constr 1 [B #6465616462656566], Constr 1 []]
                     , Map []
                     , Constr 2
                         [ Constr 0
                             [ Constr 0 [Constr 0 [B #], Constr 1 []]
                             , Constr 0 [B #24, B #746573742d6173736574]
                             , I 1000
                             , I 0
                             , I 100
                             , I 10
                             , I 10 ] ]
                     , Constr 1 [] ] ] ]
         , List []
         , List []
         , I 0
         , Map []
         , List []
         , Map []
         , Constr 0
             [ Constr 0 [Constr 1 [I 110], Constr 1 []]
             , Constr 0 [Constr 1 [I 1100], Constr 1 []] ]
         , List [B #]
         , Map
             [ ( Constr 1
                   [ Constr 0
                       [ B #058fdca70be67c74151cea3846be7f73342d92c0090b62c1052e6790ad83f145
                       , I 0 ] ]
             , Constr 1 [] ) ]
         , Map []
         , B #6465616462656566
         , Map []
         , List []
         , Constr 1 []
         , Constr 1 [] ]
     , Constr 1 []
     , Constr 1
         [ Constr 0
             [ B #058fdca70be67c74151cea3846be7f73342d92c0090b62c1052e6790ad83f145
             , I 0 ]
         , Constr 0
             [ Constr 0
                 [ Constr 0 [Constr 0 [B #], Constr 1 []]
                 , Constr 0 [B #24, B #746573742d6173736574]
                 , I 1000
                 , I 0
                 , I 100
                 , I 10
                 , I 10 ] ] ] ])