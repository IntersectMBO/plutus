{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns -fno-warn-name-shadowing -fno-warn-unused-do-bind #-}

module Spec.Marlowe.ACTUS.QCGenerator where

import qualified Data.List                                         as L
import qualified Data.Map                                          as M
import           Data.Maybe                                        (catMaybes)
import           Data.Time
import           Data.Time.Clock.POSIX                             (posixSecondsToUTCTime)
import           Data.Time.Clock.System                            (SystemTime (MkSystemTime), utcToSystemTime)
import           Language.Marlowe.ACTUS.Analysis
import           Language.Marlowe.ACTUS.Definitions.BusinessEvents
import           Language.Marlowe.ACTUS.Definitions.ContractTerms
import           Language.Marlowe.ACTUS.Definitions.Schedule
import           Test.QuickCheck

largeamount :: Gen Double
largeamount = choose (0.0, 10000000.0)

smallamount :: Gen Double
smallamount = choose (0.0, 1000.0)

percentage :: Gen Double
percentage = choose (0.0, 100.0)

scalingFactor :: Gen Double
scalingFactor = choose (0.0, 100.0)

mightbe :: Gen a -> Gen (Maybe a)
mightbe original = oneof [ Just <$> original, return Nothing ]

zeroOr :: Gen Double -> Gen Double
zeroOr original = oneof [return 0.0, original]

oneOr :: Gen Double -> Gen Double
oneOr original = oneof [return 1.0, original]

anchor :: Integer
anchor = 1577836800 -- 2020-01-01T00:00:00

maxDate :: Integer
maxDate = 1893456000 -- 2030-01-01T00:00:00

secondsPerYear :: Integer
secondsPerYear = 31557600

date :: Gen LocalTime
date = epochToLocalTime <$> choose (anchor, maxDate)

dateBefore :: LocalTime -> Gen LocalTime
dateBefore d = epochToLocalTime <$> choose (anchor, localTime d)

localTime :: LocalTime -> Integer
localTime LocalTime {..} =
  let (MkSystemTime secs _) = utcToSystemTime (UTCTime localDay (timeOfDayToTime localTimeOfDay))
   in fromIntegral secs

epochToLocalTime :: Integer -> LocalTime
epochToLocalTime = utcToLocalTime utc . posixSecondsToUTCTime . fromIntegral

cyclePeriodFreq :: Gen Period
cyclePeriodFreq =
  frequency
    [ (1, return P_D),
      (10, return P_W),
      (20, return P_M),
      (5, return P_Q),
      (5, return P_H),
      (70, return P_Y)
    ]

datecycle :: Gen Cycle
datecycle = Cycle <$> sized (\n -> choose (1, max 1 (maxDate `div` (toInteger n+1 * secondsPerYear)))) <*> cyclePeriodFreq <*> elements [ShortStub, LongStub] <*> elements [True, False]

contractTermsGen :: Gen ContractTerms
contractTermsGen = elements [PAM, LAM, NAM, ANN] >>= contractTermsGen'

contractTermsGen' :: CT -> Gen ContractTerms
contractTermsGen' ct = do
  -- initial exchange date is fixed
  let ied = epochToLocalTime anchor

  -- set the status date before initial exchange date
  let sd = LocalTime (addDays (-2) $ localDay ied) (localTimeOfDay ied)

  interest <- percentage
  notional <- largeamount
  pdied <- zeroOr smallamount

  feeBasis <- elements [FEB_A, FEB_N]
  feeRate <- zeroOr percentage

  penaltytype <- elements [PYTP_A, PYTP_N, PYTP_I, PYTP_O]
  penaltyrate <- zeroOr percentage

  eomc <- elements [EOMC_EOM, EOMC_SD]
  bdc <- elements [BDC_NULL, BDC_SCF, BDC_SCMF, BDC_CSF, BDC_CSMF, BDC_SCP, BDC_SCMP, BDC_CSP, BDC_CSMP]
  calendar <- elements [CLDR_NC] -- TODO: add CLDR_MF
  dcc <- elements [DCC_A_AISDA, DCC_A_360, DCC_A_365, DCC_E30_360ISDA, DCC_E30_360] -- TODO: DCC_B_252 is not implemented
  ppef <- elements [PPEF_N, PPEF_A, PPEF_M]
  cntrl <- elements [CR_BUY, CR_SEL]

  scef <- elements [SE_000, SE_0N0, SE_00M, SE_0NM, SE_I00, SE_IN0, SE_I0M, SE_INM]
  sccdd <- oneOr scalingFactor
  scied <- oneOr scalingFactor
  scip <- oneOr scalingFactor
  scnt <- oneOr scalingFactor

  rrsp <- zeroOr percentage
  rrmlt <- oneOr scalingFactor
  rrpf <- zeroOr percentage
  rrpc <- oneOr percentage
  rrlc <- oneOr percentage
  rrlf <- zeroOr percentage

  -- always set a maturity date
  maturityDate <- date
  amortizationDate <- case ct of
    ANN -> mightbe date
    _   -> return Nothing
  terminationDate <- mightbe date

  let upperBound = minimum $ catMaybes [Just maturityDate, amortizationDate, terminationDate]

  nextPrincipalRedemption <- case ct of
    PAM -> return Nothing
    _   -> Just <$> largeamount
  purchaseDate <- mightbe $ dateBefore upperBound
  priceAtTerminationDate <- smallamount
  priceAtPurchaseDate <- smallamount

  optionalityCycle <- mightbe datecycle
  optionalityAnchor <- mightbe $ dateBefore upperBound

  scalingCycle <- mightbe datecycle
  scalingAnchor <- mightbe $ dateBefore upperBound

  rateResetCycle <- mightbe datecycle
  rateResetAnchor <- dateBefore upperBound
  nextRateReset <- percentage

  interestCapitalisationDate <- mightbe $ dateBefore upperBound
  interestPaymentCycle <- datecycle
  interestPaymentAnchor <- case ct of
    PAM -> Just <$> dateBefore upperBound
    _   -> mightbe $ dateBefore upperBound
  accruedInterest <- mightbe smallamount

  principalRedemptionCycle <- datecycle
  principalRedemptionAnchor <- mightbe $ dateBefore upperBound

  interestPaymentCalculationBase <- mightbe $ elements [IPCB_NT, IPCB_NTIED, IPCB_NTL]
  interestPaymentCalculationBaseAmount <- largeamount
  interestPaymentCalculationBaseCycle <- mightbe datecycle
  interestPaymentCalculationBaseAnchor <- mightbe $ dateBefore upperBound

  feeCycle <- mightbe datecycle
  feeAnchor <- mightbe $ dateBefore upperBound
  feeAccrued <- mightbe smallamount

  return
    ContractTermsPoly
      { contractId = "0",
        contractType = ct,
        ct_IED = Just ied,
        ct_SD = sd,
        ct_MD = Just maturityDate,
        ct_AD = amortizationDate,
        ct_TD = terminationDate,
        ct_PRNXT = nextPrincipalRedemption,
        ct_PRD = purchaseDate,
        ct_CNTRL = cntrl,
        ct_PDIED = Just pdied,
        ct_NT = Just notional,
        ct_PPRD = priceAtPurchaseDate <$ purchaseDate,
        ct_PTD = priceAtTerminationDate <$ terminationDate,
        ct_DCC = Just dcc,
        ct_PPEF = Just ppef,
        ct_PRF = Just PRF_PF,
        scfg =
          ScheduleConfig
            { calendar = Just calendar,
              eomc = Just eomc,
              bdc = Just bdc
            },
        -- Penalties
        ct_PYRT = Just penaltyrate,
        ct_PYTP = Just penaltytype,
        -- Optionality
        ct_OPCL = optionalityCycle,
        ct_OPANX = optionalityAnchor,
        -- Scaling:
        ct_SCIED = Just scied,
        ct_SCEF = Just scef,
        ct_SCCL = scalingCycle,
        ct_SCANX = scalingAnchor,
        ct_SCCDD = Just sccdd,
        ct_SCIP = Just scip,
        ct_SCNT = Just scnt,
        -- Rate Reset
        ct_RRCL = rateResetCycle,
        ct_RRANX = Just rateResetAnchor,
        ct_RRNXT = Just nextRateReset,
        ct_RRSP = Just rrsp,
        ct_RRMLT = Just rrmlt,
        ct_RRPF = Just rrpf,
        ct_RRPC = Just rrpc,
        ct_RRLC = Just rrlc,
        ct_RRLF = Just rrlf,
        -- Interest
        ct_IPCED = interestCapitalisationDate,
        ct_IPCL = Just interestPaymentCycle,
        ct_IPANX = interestPaymentAnchor,
        ct_IPNR = Just interest,
        ct_IPAC = accruedInterest,
        ct_PRCL = case ct of
          PAM -> Nothing
          _   -> Just principalRedemptionCycle,
        ct_PRANX = principalRedemptionAnchor,
        ct_IPCB = interestPaymentCalculationBase,
        ct_IPCBA = case interestPaymentCalculationBase of
          Just IPCB_NTIED -> Just interestPaymentCalculationBaseAmount
          _               -> Nothing,
        ct_IPCBCL = interestPaymentCalculationBaseCycle,
        ct_IPCBANX = interestPaymentCalculationBaseAnchor,
        -- Fee
        ct_FECL = feeCycle,
        ct_FEANX = feeAnchor,
        ct_FEAC = feeAccrued,
        ct_FEB = Just feeBasis,
        ct_FER = Just feeRate,
        ct_CURS = Nothing,
        ct_SCMO = Nothing,
        ct_RRMO = Nothing,
        -- enable settlement currency
        enableSettlement = False,
        constraints = Nothing,
        collateralAmount = 0
      }

riskAtTGen :: Gen RiskFactors
riskAtTGen = RiskFactorsPoly <$> percentage <*> percentage <*> percentage <*> smallamount

riskFactorsGen :: ContractTerms -> Gen (M.Map LocalTime RiskFactors)
riskFactorsGen ct = do
    let riskFactors _ _ =
         RiskFactorsPoly
            { o_rf_CURS = 1.0,
              o_rf_RRMO = 1.0,
              o_rf_SCMO = 1.0,
              pp_payoff = 0.0
            }
    let days = cashCalculationDay <$> genProjectedCashflows riskFactors ct
    rf <- vectorOf (L.length days) riskAtTGen
    return $ M.fromList $ L.zip days rf

riskFactorsGenRandomWalkGen :: ContractTerms -> Gen (M.Map LocalTime RiskFactors)
riskFactorsGenRandomWalkGen contractTerms = do
    rfs <- riskFactorsGen contractTerms
    riskAtT <- riskAtTGen
    let
        (riskFactorsDates, riskFactorsValues) = unzip $ M.toList rfs

        fluctuate state fluctiation = state + (fluctiation - 50) / 100
        walk rf st =
            let fluctuate' extractor = fluctuate (extractor rf) (extractor st)
            in RiskFactorsPoly (fluctuate' o_rf_CURS) (fluctuate' o_rf_RRMO) (fluctuate' o_rf_SCMO) (fluctuate' pp_payoff)
        path = L.scanl walk riskAtT riskFactorsValues
    return $ M.fromList $ L.zip riskFactorsDates path
