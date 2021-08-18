{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE OverloadedStrings     #-}

{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}

module Spec.Marlowe.Util where

import           Data.Aeson.Types                                  (FromJSON, Value (Array, Number, Object, String))
import           Data.HashMap.Strict                               as HashMap ((!))
import           Data.List.Extra                                   (replace)
import           Data.Map                                          as Map (Map, lookup, map, (!))
import           Data.Maybe                                        (fromJust)
import           Data.Scientific                                   (toRealFloat)
import           Data.Text                                         (unpack)
import           Data.Time                                         (Day, defaultTimeLocale, parseTimeM)
import           Data.Vector                                       as Vector (map, toList)
import           GHC.Generics                                      (Generic)
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents (DataObserved, EventType,
                                                                    ValueObserved (ValueObserved, timestamp, value),
                                                                    ValuesObserved (ValuesObserved, identifier, values))
import           Language.Marlowe.ACTUS.Definitions.ContractTerms
import           Language.Marlowe.ACTUS.Definitions.Schedule       (CashFlow (CashFlow, amount, cashEvent, cashPaymentDay))
import           Test.Tasty.HUnit                                  (assertBool)

data TestResult = TestResult{
    eventDate           :: String
  , eventType           :: String
  , payoff              :: Double
  , currency            :: String
  , notionalPrincipal   :: Double
  , nominalInterestRate :: Double
  , accruedInterest     :: Double
}
  deriving stock (Show, Generic)
  deriving anyclass (FromJSON)

data TestCase = TestCase{
    identifier     :: String
  , terms          :: Map String Value
  , to             :: String
  , dataObserved   :: Map String Value
  , eventsObserved :: Value
  , results        :: [TestResult]
}
  deriving stock (Show, Generic)
  deriving anyclass (FromJSON)

termsToString :: Map String Value -> Map String String
termsToString = Map.map (\case
  String t -> unpack t
  Number t -> show (toRealFloat t :: Double))

parseObservedValues :: Map String Value -> DataObserved
parseObservedValues =
  Map.map(\(Object valuesObserved) ->
    let String identifier = valuesObserved HashMap.! "identifier"
        Array values = valuesObserved HashMap.! "data"
    in
      ValuesObserved{
        identifier = unpack identifier
      , values = Vector.toList $
          Vector.map (\(Object observedValue) ->
            let String timestamp = observedValue HashMap.! "timestamp"
                String value = observedValue HashMap.! "value"
            in
              ValueObserved{
                timestamp = fromJust $ parseMaybeDate $ Just $ unpack timestamp
              , value = read (unpack value) :: Double
              }
          ) values
      }
  )

assertTestResults :: [CashFlow] -> [TestResult] -> String -> IO ()
assertTestResults [] [] _ = return ()
assertTestResults (cashFlow: restCash) (testResult: restTest) identifier = do
  assertTestResult cashFlow testResult identifier
  assertTestResults restCash restTest identifier

assertTestResult :: CashFlow -> TestResult -> String -> IO ()
assertTestResult
  CashFlow{cashPaymentDay = date, cashEvent = event, amount = payoff}
  testResult@TestResult{eventDate = testDate, eventType = testEvent, payoff = testPayoff} identifier = do
    assertBool ("[" ++ show identifier ++ "] Generated event and test event types should be the same: actual " ++ show event ++ ", expected for " ++ show testResult) $ event == (read testEvent :: EventType)
    assertBool ("Generated date and test date should be the same: expected " ++ show testDate ++ ", actual " ++ show date ++ " in " ++ identifier) (date == (fromJust $ parseDate testDate))
    assertBool ("[" ++ show identifier ++ "]  Generated payoff and test payoff should be the same: actual " ++ show payoff ++ ", expected for " ++ show testResult) $ (realToFrac payoff :: Float) == (realToFrac testPayoff :: Float)

testToContractTerms :: TestCase -> ContractTerms
testToContractTerms TestCase{terms = terms} =
  let terms' = termsToString terms
  in ContractTerms
     {
       contractId       = terms' Map.! "contractID"
     , contractType     = read $ terms' Map.! "contractType" :: CT
     , ct_CNTRL         = read $ "CR_" ++ terms' Map.! "contractRole" :: CR
     , ct_CURS          = Map.lookup "settlementCurrency" terms'
     , ct_IED           = parseMaybeDate $ Map.lookup "initialExchangeDate" terms'
     , ct_DCC           = maybeDCCFromString $ Map.lookup "dayCountConvention" terms'
     , scfg             = ScheduleConfig {
                             calendar = readMaybe (maybeConcatPrefix "CLDR_" (Map.lookup "calendar" terms')) :: Maybe Calendar
                           , eomc = readMaybe (maybeConcatPrefix "EOMC_" (Map.lookup "endOfMonthConvention" terms')) :: Maybe EOMC
                           , bdc = readMaybe (maybeConcatPrefix "BDC_" (Map.lookup "businessDayConvention" terms')) :: Maybe BDC
                          }
     , ct_SD            = fromJust $ parseDate (terms' Map.! "statusDate")
     , ct_PRF           = readMaybe (maybeConcatPrefix "PRF_" (Map.lookup "contractPerformance" terms')) :: Maybe PRF
     , ct_FECL          = parseMaybeCycle $ Map.lookup "cycleOfFee" terms'
     , ct_FEANX         = parseMaybeDate $ Map.lookup "cycleAnchorDateOfFee" terms'
     , ct_FEAC          = readMaybe $ Map.lookup "feeAccrued" terms' :: Maybe Double
     , ct_FEB           = readMaybe (maybeConcatPrefix "FEB_" (Map.lookup "feeBasis" terms')) :: Maybe FEB
     , ct_FER           = readMaybe $ Map.lookup "feeRate" terms' :: Maybe Double
     , ct_IPANX         = parseMaybeDate $ Map.lookup "cycleAnchorDateOfInterestPayment" terms'
     , ct_IPCL          = parseMaybeCycle $ Map.lookup "cycleOfInterestPayment" terms'
     , ct_IPAC          = readMaybe $ Map.lookup "accruedInterest" terms' :: Maybe Double
     , ct_IPCED         = parseMaybeDate $ Map.lookup "capitalizationEndDate" terms'
     , ct_IPCBANX       = parseMaybeDate $ Map.lookup "cycleAnchorDateOfInterestCalculationBase" terms'
     , ct_IPCBCL        = parseMaybeCycle $ Map.lookup "cycleOfInterestCalculationBase" terms'
     , ct_IPCB          = readMaybe (maybeConcatPrefix "IPCB_" (Map.lookup "interestCalculationBase" terms')) :: Maybe IPCB
     , ct_IPCBA         = readMaybe $ Map.lookup "interestCalculationBaseAmount" terms' :: Maybe Double
     , ct_IPNR          = readMaybe $ Map.lookup "nominalInterestRate" terms' :: Maybe Double
     , ct_NT            = readMaybe $ Map.lookup "notionalPrincipal" terms' :: Maybe Double
     , ct_PDIED         = readMaybe $ Map.lookup "premiumDiscountAtIED" terms' :: Maybe Double
     , ct_MD            = parseMaybeDate $ Map.lookup "maturityDate" terms'
     , ct_PRANX         = parseMaybeDate $ Map.lookup "cycleAnchorDateOfPrincipalRedemption" terms'
     , ct_PRCL          = parseMaybeCycle $ Map.lookup "cycleOfPrincipalRedemption" terms'
     , ct_PRNXT         = readMaybe $ Map.lookup "nextPrincipalRedemptionPayment" terms' :: Maybe Double
     , ct_PRD           = parseMaybeDate $ Map.lookup "purchaseDate" terms'
     , ct_PPRD          = readMaybe $ Map.lookup "priceAtPurchaseDate" terms' :: Maybe Double
     , ct_TD            = parseMaybeDate $ Map.lookup "terminationDate" terms'
     , ct_PTD           = readMaybe $ Map.lookup "priceAtTerminationDate" terms' :: Maybe Double
     , ct_SCIED         = readMaybe $ Map.lookup "scalingIndexAtStatusDate" terms' :: Maybe Double
     , ct_SCANX         = parseMaybeDate $ Map.lookup "cycleAnchorDateOfScalingIndex" terms'
     , ct_SCCL          = parseMaybeCycle $ Map.lookup "cycleOfScalingIndex" terms'
     , ct_SCEF          = readMaybe (maybeReplace "O" "0" (maybeConcatPrefix "SE_" (Map.lookup "scalingEffect" terms'))) :: Maybe SCEF
     , ct_SCCDD         = readMaybe $ Map.lookup "scalingIndexAtContractDealDate" terms' :: Maybe Double
     , ct_SCMO          = Map.lookup "marketObjectCodeOfScalingIndex" terms'
     , ct_OPCL          = parseMaybeCycle $ Map.lookup "cycleOfOptionality" terms'
     , ct_OPANX         = parseMaybeDate $ Map.lookup "cycleAnchorDateOfOptionality" terms'
     , ct_PYRT          = readMaybe $ Map.lookup "penaltyRate" terms' :: Maybe Double
     , ct_PYTP          = readMaybe (maybeConcatPrefix "PYTP_" (Map.lookup "penaltyType" terms')) :: Maybe PYTP
     , ct_PPEF          = readMaybe (maybeConcatPrefix "PPEF_" (Map.lookup "prepaymentEffect" terms')) :: Maybe PPEF
     , ct_cPYRT         = 0.0
     , ct_RRCL          = parseMaybeCycle $ Map.lookup "cycleOfRateReset" terms'
     , ct_RRANX         = parseMaybeDate $ Map.lookup "cycleAnchorDateOfRateReset" terms'
     , ct_RRNXT         = readMaybe $ Map.lookup "nextResetRate" terms' :: Maybe Double
     , ct_RRSP          = readMaybe $ Map.lookup "rateSpread" terms' :: Maybe Double
     , ct_RRMLT         = readMaybe $ Map.lookup "rateMultiplier" terms' :: Maybe Double
     , ct_RRPF          = readMaybe $ Map.lookup "periodFloor" terms' :: Maybe Double
     , ct_RRPC          = readMaybe $ Map.lookup "periodCap" terms' :: Maybe Double
     , ct_RRLC          = readMaybe $ Map.lookup "lifeCap" terms' :: Maybe Double
     , ct_RRLF          = readMaybe $ Map.lookup "lifeFloor" terms' :: Maybe Double
     , ct_RRMO          = Map.lookup "marketObjectCodeOfRateReset" terms'
     , enableSettlement = False
     , constraints      = Nothing
     , collateralAmount = 0
     }

readMaybe :: (Read a) => Maybe String -> Maybe a
readMaybe = fmap read

parseMaybeDate :: Maybe String -> Maybe Day
parseMaybeDate = maybe Nothing parseDate

parseDate :: String -> Maybe Day
parseDate date =
  let format | length date == 19 = "%Y-%-m-%-dT%T"
             | otherwise = "%Y-%-m-%-dT%H:%M"
  in
    parseTimeM True defaultTimeLocale format date :: Maybe Day

parseMaybeCycle :: Maybe String -> Maybe Cycle
parseMaybeCycle stringCycle =
  case stringCycle of
    Just (_:stringCycle') ->
      let n = read (takeWhile (< 'A') stringCycle') :: Integer
          [p, _, s] = dropWhile (< 'A') stringCycle'
      in
          Just Cycle { n = n, p = read $ "P_" ++ [p] :: Period, stub = parseStub [s], includeEndDay = False }
    Nothing ->
      Nothing

parseStub :: String -> Stub
parseStub "0" = LongStub
parseStub "1" = ShortStub

maybeDCCFromString :: Maybe String -> Maybe DCC
maybeDCCFromString dcc =
  let parseDCC "AA"     = Just DCC_A_AISDA
      parseDCC "A360"   = Just DCC_A_360
      parseDCC "A365"   = Just DCC_A_365
      parseDCC "30E360" = Just DCC_E30_360
      parseDCC _        = Nothing
  in dcc >>= parseDCC

maybeConcatPrefix :: String -> Maybe String -> Maybe String
maybeConcatPrefix prefix = fmap (prefix ++)

maybeReplace :: String -> String -> Maybe String -> Maybe String
maybeReplace from to = fmap (replace from to)
