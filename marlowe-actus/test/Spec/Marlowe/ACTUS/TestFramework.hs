{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeSynonymInstances  #-}

module Spec.Marlowe.ACTUS.TestFramework
  where

import           Control.Applicative                               ((<|>))
import           Control.Monad                                     (mzero)
import           Data.Aeson
import           Data.ByteString.Lazy.UTF8                         as BLU (fromString)
import           Data.Char                                         (toUpper)
import           Data.List                                         as L (find)
import           Data.List.Extra                                   (replace)
import           Data.Map                                          as Map (Map, lookup, mapMaybe, toList, (!))
import           Data.Maybe                                        (fromJust, fromMaybe, maybeToList)
import           Data.Scientific                                   (toRealFloat)
import           Data.Text                                         (unpack)
import           Data.Time                                         (LocalTime (..), defaultTimeLocale, parseTimeM)
import           Data.Vector                                       as Vector (head)
import           GHC.Generics                                      (Generic)
import           GHC.Records                                       (getField)
import           Language.Marlowe.ACTUS.Analysis
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents
import           Language.Marlowe.ACTUS.Definitions.ContractTerms  hiding (Assertion)
import           Language.Marlowe.ACTUS.Definitions.Schedule
import           Language.Marlowe.ACTUS.Model.Utility.DateShift    (getFollowingBusinessDay)
import           Test.Tasty
import           Test.Tasty.HUnit                                  (Assertion, assertBool, assertFailure, testCase)

tests :: String -> [TestCase] -> TestTree
tests n t = testGroup n $ [ testCase (getField @"identifier" tc) (runTest tc) | tc <- t]

runTest :: TestCase -> Assertion
runTest tc@TestCase {..} =
  let testcase = testToContractTerms tc
      contract = setDefaultContractTermValues testcase

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
            observedKey DV = Just (fmap toUpper identifier ++ "_DV")
            observedKey XD = let c = Prelude.head (contractStructure contract) in Just $ marketObjectCode c
            observedKey _  = ct_CURS contract

            value = fromMaybe 1.0 $ do
              k <- observedKey ev
              DataObserved {values = values} <- Map.lookup k dataObserved
              ValueObserved {value = valueObserved} <- L.find (\ValueObserved {timestamp = timestamp} ->
                getFollowingBusinessDay timestamp (fromJust $ calendar $ scfg contract) == date) values
              return valueObserved
         in case ev of
              RR -> riskFactors {o_rf_RRMO = value}
              SC -> riskFactors {o_rf_SCMO = value}
              DV -> riskFactors {pp_payoff = value}
              XD -> riskFactors {pp_payoff = value}
              _  -> riskFactors {o_rf_CURS = value}

      cashFlows = genProjectedCashflows getRiskFactors contract
      cashFlowsTo = maybe cashFlows (\d -> filter (\cf -> cashCalculationDay cf <= d) cashFlows) (parseDate to)
   in assertTestResults cashFlowsTo results identifier

testCasesFromFile :: [String] -> FilePath -> IO [TestCase]
testCasesFromFile excludedTestCases fileName = do
  tcs <- readFile fileName
  case let tc = fromString tcs in eitherDecode tc :: Either String (Map String TestCase) of
    (Right decodedTests) ->
      return $
        filter (\TestCase {..} -> notElem identifier excludedTestCases) $
          fmap snd (Map.toList decodedTests)
    Left e -> assertFailure ("Cannot parse test specification from file: " ++ fileName ++ "\nError: " ++ e) >> return []

assertTestResults :: [CashFlow] -> [TestResult] -> String -> IO ()
assertTestResults [] [] _ = return ()
assertTestResults (cashFlow : restCash) (testResult : restTest) identifier' = do
  assertTestResult cashFlow testResult identifier'
  assertTestResults restCash restTest identifier'
assertTestResults _ _ _ = assertFailure "Sizes differ"

assertTestResult :: CashFlow -> TestResult -> String -> IO ()
assertTestResult
  CashFlow {cashPaymentDay = date, cashEvent = event, amount = payoff'}
  testResult@TestResult {eventDate = testDate, eventType = testEvent, payoff = testPayoff}
  identifier' = do

    assertBool
      ("[" ++ show identifier' ++ "] Generated event and test event types should be the same: actual " ++ show event ++ ", expected for " ++ show testResult)
      $ event == (read testEvent :: EventType)

    assertBool
      ("Generated date and test date should be the same: actual " ++ show date ++ ", expected for " ++ show testResult ++ " in " ++ identifier')
      $ date == (fromJust $ parseDate testDate)

    assertBool
      ("[" ++ show identifier' ++ "]  Generated payoff and test payoff should be the same: actual " ++ show payoff' ++ ", expected for " ++ show testResult)
      $ (realToFrac payoff' :: Float) == (realToFrac testPayoff :: Float)

data DataObserved = DataObserved
  { identifier :: String
  , values     :: [ValueObserved]
  }
  deriving stock (Show, Generic)

instance FromJSON DataObserved where
  parseJSON (Object v) =
    DataObserved
      <$> v .: "identifier"
      <*> v .: "data"
  parseJSON _ = mzero

data ValueObserved = ValueObserved
  { timestamp :: LocalTime
  , value     :: Double
  }
  deriving stock (Show, Generic)

instance FromJSON ValueObserved where
  parseJSON (Object v) =
    ValueObserved
      <$> v .: "timestamp"
      <*> (v .: "value" <|> (read <$> v.: "value"))
  parseJSON _ = mzero

data TestResult = TestResult
  { eventDate           :: String,
    eventType           :: String,
    payoff              :: Double,
    currency            :: String,
    notionalPrincipal   :: Double,
    exerciseAmount      :: Maybe Double,
    nominalInterestRate :: Maybe Double,
    accruedInterest     :: Maybe Double
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
      <*> v .:? "exerciseAmount"
      <*> (v .:? "nominalInterestRate" <|> (fmap read <$> v.:? "nominalInterestRate"))
      <*> (v .:? "accruedInterest" <|> (fmap read <$> v.:? "accruedInterest"))
  parseJSON _ = mzero

data TestCase = TestCase
  { identifier     :: String,
    terms          :: Map String Value,
    to             :: String,
    dataObserved   :: Map String DataObserved,
    eventsObserved :: Value,
    results        :: [TestResult]
  }
  deriving stock (Show, Generic)
  deriving anyclass (FromJSON)

-- TODO: refactor JSON parsing of ContractTerms (see: SCP-2881)
testToContractTerms :: TestCase -> ContractTerms
testToContractTerms TestCase{terms = t} =
  let terms' = termsToString t
  in ContractTermsPoly
     {
       contractId        = terms' Map.! "contractID"
     , contractType      = handleResult . fromJSON $ t Map.! "contractType" :: CT
     , contractStructure = maybeToList $ toContractStructure <$> Map.lookup "contractStructure" t
     , ct_CNTRL          = handleResult . fromJSON $ t Map.! "contractRole" :: CR
     , ct_CURS           = handleResult . fromJSON <$> Map.lookup "currency" t
     , ct_IED            = parseDate =<< Map.lookup "initialExchangeDate" terms'
     , ct_DCC            = handleResult . fromJSON <$> Map.lookup "dayCountConvention" t
     , scfg              = ScheduleConfig {
                              calendar = handleResult . fromJSON <$> Map.lookup "calendar" t :: Maybe Calendar
                            , eomc = handleResult . fromJSON <$> Map.lookup "endOfMonthConvention" t :: Maybe EOMC
                            , bdc = handleResult . fromJSON <$> Map.lookup "businessDayConvention" t :: Maybe BDC
                           }
     , ct_SD             = fromJust $ parseDate (terms' Map.! "statusDate")
     , ct_PRF            = handleResult . fromJSON <$> Map.lookup "contractPerformance" t :: Maybe PRF
     , ct_FECL           = handleResult . fromJSON <$> Map.lookup "cycleOfFee" t
     , ct_FEANX          = parseDate =<< Map.lookup "cycleAnchorDateOfFee" terms'
     , ct_FEAC           = handleResult . fromJSON <$> Map.lookup "feeAccrued" t :: Maybe Double
     , ct_FEB            = handleResult . fromJSON <$> Map.lookup "feeBasis" t :: Maybe FEB
     , ct_FER            = read <$> Map.lookup "feeRate" terms' :: Maybe Double
     , ct_IPANX          = parseDate =<< Map.lookup "cycleAnchorDateOfInterestPayment" terms'
     , ct_IPCL           = handleResult . fromJSON <$> Map.lookup "cycleOfInterestPayment" t
     , ct_IPAC           = read <$> Map.lookup "accruedInterest" terms' :: Maybe Double
     , ct_IPCED          = parseDate =<< Map.lookup "capitalizationEndDate" terms'
     , ct_IPCBANX        = parseDate =<< Map.lookup "cycleAnchorDateOfInterestCalculationBase" terms'
     , ct_IPCBCL         = handleResult . fromJSON <$> Map.lookup "cycleOfInterestCalculationBase" t
     , ct_IPCB           = handleResult . fromJSON <$> Map.lookup "interestCalculationBase" t :: Maybe IPCB
     , ct_IPCBA          = read <$> Map.lookup "interestCalculationBaseAmount" terms' :: Maybe Double
     , ct_IPNR           = read <$> Map.lookup "nominalInterestRate" terms' :: Maybe Double
     , ct_SCIP           = read <$> Map.lookup "interestScalingMultiplier" terms' :: Maybe Double
     , ct_NT             = read <$> Map.lookup "notionalPrincipal" terms' :: Maybe Double
     , ct_PDIED          = read <$> Map.lookup "premiumDiscountAtIED" terms' :: Maybe Double
     , ct_MD             = parseDate =<< Map.lookup "maturityDate" terms'
     , ct_AD             = parseDate =<< Map.lookup "amortizationDate" terms'
     , ct_PRANX          = parseDate =<< Map.lookup "cycleAnchorDateOfPrincipalRedemption" terms'
     , ct_PRCL           = handleResult . fromJSON <$> Map.lookup "cycleOfPrincipalRedemption" t
     , ct_PRNXT          = read <$> Map.lookup "nextPrincipalRedemptionPayment" terms' :: Maybe Double
     , ct_PRD            = parseDate =<< Map.lookup "purchaseDate" terms'
     , ct_PPRD           = read <$> Map.lookup "priceAtPurchaseDate" terms' :: Maybe Double
     , ct_TD             = parseDate =<< Map.lookup "terminationDate" terms'
     , ct_PTD            = read <$> Map.lookup "priceAtTerminationDate" terms' :: Maybe Double
     , ct_SCIED          = read <$> Map.lookup "scalingIndexAtStatusDate" terms' :: Maybe Double
     , ct_SCANX          = parseDate =<< Map.lookup "cycleAnchorDateOfScalingIndex" terms'
     , ct_SCCL           = handleResult . fromJSON <$> Map.lookup "cycleOfScalingIndex" t
     , ct_SCEF           = read <$> (replace "O" "0" . ("SE_" ++) <$> Map.lookup "scalingEffect" terms') :: Maybe SCEF
     , ct_SCCDD          = read <$> Map.lookup "scalingIndexAtContractDealDate" terms' :: Maybe Double
     , ct_SCMO           = Map.lookup "marketObjectCodeOfScalingIndex" terms'
     , ct_SCNT           = read <$> Map.lookup "notionalScalingMultiplier" terms' :: Maybe Double
     , ct_OPCL           = handleResult . fromJSON <$> Map.lookup "cycleOfOptionality" t
     , ct_OPANX          = parseDate =<< Map.lookup "cycleAnchorDateOfOptionality" terms'
     , ct_PYRT           = read <$> Map.lookup "penaltyRate" terms' :: Maybe Double
     , ct_PYTP           = handleResult . fromJSON <$> Map.lookup "penaltyType" t :: Maybe PYTP
     , ct_PPEF           = handleResult . fromJSON <$> Map.lookup "prepaymentEffect" t :: Maybe PPEF
     , ct_RRCL           = handleResult . fromJSON <$> Map.lookup "cycleOfRateReset" t
     , ct_RRANX          = parseDate =<< Map.lookup "cycleAnchorDateOfRateReset" terms'
     , ct_RRNXT          = read <$> Map.lookup "nextResetRate" terms' :: Maybe Double
     , ct_RRSP           = read <$> Map.lookup "rateSpread" terms' :: Maybe Double
     , ct_RRMLT          = read <$> Map.lookup "rateMultiplier" terms' :: Maybe Double
     , ct_RRPF           = read <$> Map.lookup "periodFloor" terms' :: Maybe Double
     , ct_RRPC           = read <$> Map.lookup "periodCap" terms' :: Maybe Double
     , ct_RRLC           = read <$> Map.lookup "lifeCap" terms' :: Maybe Double
     , ct_RRLF           = read <$> Map.lookup "lifeFloor" terms' :: Maybe Double
     , ct_RRMO           = Map.lookup "marketObjectCodeOfRateReset" terms'
     , ct_DVANX          = parseDate =<< Map.lookup "cycleAnchorDateOfDividendPayment" terms'
     , ct_DVCL           = handleResult . fromJSON <$> Map.lookup "cycleOfDividendPayment" t
     , ct_DVNP           = read <$> Map.lookup "nextDividendPaymentAmount" terms' :: Maybe Double
     , ct_OPTP           = handleResult . fromJSON <$> Map.lookup "optionType" t :: Maybe OPTP
     , ct_OPS1           = read <$> Map.lookup "optionStrike1" terms' :: Maybe Double
     , ct_OPXT           = handleResult . fromJSON <$> Map.lookup "optionExerciseType" t :: Maybe OPXT
     , ct_STP            = handleResult . fromJSON <$> Map.lookup "settlementPeriod" t
     , ct_XA             = read <$> Map.lookup "exerciseAmount" terms' :: Maybe Double
     , ct_DS             = handleResult . fromJSON <$> Map.lookup "deliverySettlement" t :: Maybe DS
     , ct_XD             = parseDate =<< Map.lookup "exerciseDate" terms'
     , ct_PFUT           = read <$> Map.lookup "futuresPrice" terms' :: Maybe Double
     , enableSettlement  = False
     , constraints       = Nothing
     , collateralAmount  = 0
     }
  where
    termsToString :: Map String Value -> Map String String
    termsToString = Map.mapMaybe valueToString
      where
        valueToString :: Value -> Maybe String
        valueToString (String s) = Just $ unpack s
        valueToString (Number s) = Just $ show (toRealFloat s :: Double)
        valueToString _          = Nothing

    toContractStructure :: Value -> ContractStructure
    toContractStructure (Array a) = handleResult $ fromJSON (Vector.head a)
    toContractStructure _         = error "Error parsing ContractStructure"

    handleResult :: Result a -> a
    handleResult (Success s) = s
    handleResult (Error err) = error err

parseDate :: String -> Maybe LocalTime
parseDate date =
  let format
        | length date == 19 = "%Y-%-m-%-dT%T"
        | otherwise = "%Y-%-m-%-dT%H:%M"
   in parseTimeM True defaultTimeLocale format date :: Maybe LocalTime
