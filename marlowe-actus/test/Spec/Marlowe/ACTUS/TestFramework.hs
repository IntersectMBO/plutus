{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE TypeApplications      #-}

module Spec.Marlowe.ACTUS.TestFramework
  where

import           Control.Applicative                               ((<|>))
import           Control.Monad                                     (mzero)
import           Data.Aeson
import           Data.ByteString.Lazy.UTF8                         as BLU (fromString)
import           Data.HashMap.Strict                               as HashMap ((!))
import           Data.List                                         as L (find)
import           Data.List.Extra                                   (replace)
import           Data.Map                                          as Map (Map, lookup, mapMaybe, toList, (!))
import           Data.Maybe                                        (fromJust, fromMaybe)
import           Data.Scientific                                   (toRealFloat)
import           Data.Text                                         (unpack)
import           Data.Time                                         (LocalTime (..), defaultTimeLocale, parseTimeM)
import           Data.Vector                                       as Vector (catMaybes, map, toList)
import           GHC.Generics                                      (Generic)
import           GHC.Records                                       (getField)
import           Language.Marlowe.ACTUS.Analysis
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents
import           Language.Marlowe.ACTUS.Definitions.ContractTerms  hiding (Assertion)
import           Language.Marlowe.ACTUS.Definitions.Schedule
import           Test.Tasty
import           Test.Tasty.HUnit                                  (Assertion, assertBool, assertFailure, testCase)

tests :: String -> [TestCase] -> TestTree
tests n t = testGroup n $ [ testCase (getField @"identifier" tc) (runTest tc) | tc <- t]

runTest :: TestCase -> Assertion
runTest tc@TestCase {..} =
  let testcase = testToContractTerms tc
      contract = setDefaultContractTermValues testcase
      observed = parseObservedValues dataObserved

      getRiskFactors ev date =
        let riskFactors =
              RiskFactorsPoly
                { o_rf_CURS = 1.0,
                  o_rf_RRMO = 1.0,
                  o_rf_SCMO = 1.0,
                  pp_payoff = 0.0
                }

            observedKey RR = ct_RRMO contract
            observedKey SC = ct_SCMO contract
            observedKey _  = ct_CURS contract

            value = fromMaybe 1.0 $ do
              k <- observedKey ev
              ValuesObserved {values = values} <- Map.lookup k observed
              ValueObserved {value = valueObserved} <- L.find (\ValueObserved {timestamp = timestamp} -> timestamp == date) values
              return valueObserved
         in case ev of
              RR -> riskFactors {o_rf_RRMO = value}
              SC -> riskFactors {o_rf_SCMO = value}
              _  -> riskFactors {o_rf_CURS = value}

      cashFlows = genProjectedCashflows getRiskFactors contract
      cashFlowsTo = maybe cashFlows (\d -> filter (\cf -> cashCalculationDay cf <= d) cashFlows) (parseDate to)
   in assertTestResults cashFlowsTo results identifier

testCasesFromFile :: [String] -> FilePath -> IO [TestCase]
testCasesFromFile excludedTestCases fileName = do
  tcs <- readFile fileName
  case let tc = fromString tcs in decode tc :: Maybe (Map String TestCase) of
    (Just decodedTests) ->
      return $
        filter (\TestCase {..} -> notElem identifier excludedTestCases) $
          fmap snd (Map.toList decodedTests)
    Nothing -> assertFailure ("Cannot parse test specification from file: " ++ fileName) >> return []

data ValuesObserved = ValuesObserved
  { identifier :: String
  , values     :: [ValueObserved]
  }
  deriving (Show)

data ValueObserved = ValueObserved
  { timestamp :: LocalTime
  , value     :: Double
  }
  deriving (Show)

data TestResult = TestResult
  { eventDate           :: String,
    eventType           :: String,
    payoff              :: Double,
    currency            :: String,
    notionalPrincipal   :: Double,
    nominalInterestRate :: Double,
    accruedInterest     :: Double
  }
  deriving stock (Show, Generic)

-- types are inconsistent in json files for NAM and ANN
-- test cases in https://github.com/actusfrf/actus-tests/tree/master/tests
instance FromJSON TestResult where
  parseJSON (Object v) =
    TestResult
      <$> v .: "eventDate"
      <*> v .: "eventType"
      <*> (v .: "payoff" <|> (read <$> v .: "payoff"))
      <*> v .: "currency"
      <*> (v .: "notionalPrincipal" <|> (read <$> v.: "notionalPrincipal"))
      <*> (v .: "nominalInterestRate" <|> (read <$> v.: "nominalInterestRate"))
      <*> (v .: "accruedInterest" <|> (read <$> v.: "accruedInterest"))
  parseJSON _ = mzero

data TestCase = TestCase
  { identifier     :: String,
    terms          :: Map String Value,
    to             :: String,
    dataObserved   :: Map String Value,
    eventsObserved :: Value,
    results        :: [TestResult]
  }
  deriving stock (Show, Generic)
  deriving anyclass (FromJSON)

termsToString :: Map String Value -> Map String String
termsToString = Map.mapMaybe valueToString
  where
    valueToString :: Value -> Maybe String
    valueToString (String t) = Just $ unpack t
    valueToString (Number t) = Just $ show (toRealFloat t :: Double)
    valueToString _          = Nothing

valueToObserved :: Value -> Maybe ValuesObserved
valueToObserved (Object valuesObserved) = do
  case valuesObserved HashMap.! "identifier" of
    String identifier' ->
      case valuesObserved HashMap.! "data" of
        Array values' ->
          Just $
            ValuesObserved
              { identifier = unpack identifier',
                values = Vector.toList $ Vector.catMaybes $ Vector.map f values'
              }
        _ -> Nothing
    _ -> Nothing
  where
    f (Object observedValue) =
      case observedValue HashMap.! "timestamp" of
        String timestamp' ->
          case observedValue HashMap.! "value" of
            String value' ->
              Just $
                ValueObserved
                  { timestamp = fromJust $ parseMaybeDate $ Just $ unpack timestamp',
                    value = read (unpack value') :: Double
                  }
            _ -> Nothing
        _ -> Nothing
    f _ = Nothing
valueToObserved _ = Nothing

parseObservedValues :: Map String Value -> Map String ValuesObserved
parseObservedValues = Map.mapMaybe valueToObserved

assertTestResults :: [CashFlow] -> [TestResult] -> String -> IO ()
assertTestResults [] [] _ = return ()
assertTestResults (cashFlow: restCash) (testResult: restTest) identifier' = do
  assertTestResult cashFlow testResult identifier'
  assertTestResults restCash restTest identifier'
assertTestResults _ _ _ = assertFailure "Sizes differ"

assertTestResult :: CashFlow -> TestResult -> String -> IO ()
assertTestResult
  CashFlow{cashPaymentDay = date, cashEvent = event, amount = payoff'}
  testResult@TestResult{eventDate = testDate, eventType = testEvent, payoff = testPayoff} identifier' = do
    assertBool ("[" ++ show identifier' ++ "] Generated event and test event types should be the same: actual " ++ show event ++ ", expected for " ++ show testResult) $ event == (read testEvent :: EventType)
    assertBool ("Generated date and test date should be the same: actual " ++ show date ++ ", expected for " ++ show testResult ++ " in " ++ identifier') (date == (fromJust $ parseDate testDate))
    assertBool ("[" ++ show identifier' ++ "]  Generated payoff and test payoff should be the same: actual " ++ show payoff' ++ ", expected for " ++ show testResult) $ (realToFrac payoff' :: Float) == (realToFrac testPayoff :: Float)

testToContractTerms :: TestCase -> ContractTerms
testToContractTerms TestCase{terms = t} =
  let terms' = termsToString t
  in ContractTermsPoly
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
     , ct_SCIP          = readMaybe $ Map.lookup "interestScalingMultiplier" terms' :: Maybe Double
     , ct_NT            = readMaybe $ Map.lookup "notionalPrincipal" terms' :: Maybe Double
     , ct_PDIED         = readMaybe $ Map.lookup "premiumDiscountAtIED" terms' :: Maybe Double
     , ct_MD            = parseMaybeDate $ Map.lookup "maturityDate" terms'
     , ct_AD            = parseMaybeDate $ Map.lookup "amortizationDate" terms'
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
     , ct_SCEF          = readMaybe (replace "O" "0" <$> maybeConcatPrefix "SE_" (Map.lookup "scalingEffect" terms')) :: Maybe SCEF
     , ct_SCCDD         = readMaybe $ Map.lookup "scalingIndexAtContractDealDate" terms' :: Maybe Double
     , ct_SCMO          = Map.lookup "marketObjectCodeOfScalingIndex" terms'
     , ct_SCNT          = readMaybe $ Map.lookup "notionalScalingMultiplier" terms' :: Maybe Double
     , ct_OPCL          = parseMaybeCycle $ Map.lookup "cycleOfOptionality" terms'
     , ct_OPANX         = parseMaybeDate $ Map.lookup "cycleAnchorDateOfOptionality" terms'
     , ct_PYRT          = readMaybe $ Map.lookup "penaltyRate" terms' :: Maybe Double
     , ct_PYTP          = readMaybe (maybeConcatPrefix "PYTP_" (Map.lookup "penaltyType" terms')) :: Maybe PYTP
     , ct_PPEF          = readMaybe (maybeConcatPrefix "PPEF_" (Map.lookup "prepaymentEffect" terms')) :: Maybe PPEF
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

parseMaybeDate :: Maybe String -> Maybe LocalTime
parseMaybeDate = maybe Nothing parseDate

parseDate :: String -> Maybe LocalTime
parseDate date =
  let format | length date == 19 = "%Y-%-m-%-dT%T"
             | otherwise = "%Y-%-m-%-dT%H:%M"
  in
    parseTimeM True defaultTimeLocale format date :: Maybe LocalTime

parseCycle :: String -> Maybe Cycle
parseCycle (_ : rest) =
  let n' = read (takeWhile (< 'A') rest) :: Integer
   in case dropWhile (< 'A') rest of
        [p', _, s] -> do
          stub' <- parseStub [s]
          return $ Cycle {n = n', p = read $ "P_" ++ [p'] :: Period, stub = stub', includeEndDay = False}
        _ -> Nothing
parseCycle _ = Nothing

parseMaybeCycle :: Maybe String -> Maybe Cycle
parseMaybeCycle = maybe Nothing parseCycle

parseStub :: String -> Maybe Stub
parseStub "0" = Just LongStub
parseStub "1" = Just ShortStub
parseStub _   = Nothing

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
