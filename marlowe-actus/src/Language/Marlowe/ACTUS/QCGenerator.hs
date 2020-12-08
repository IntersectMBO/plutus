{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns -fno-warn-name-shadowing -fno-warn-unused-do-bind #-}
module Language.Marlowe.ACTUS.QCGenerator where

import           Language.Marlowe.ACTUS.Definitions.ContractTerms
import           Test.QuickCheck
import           Data.Time
import           Data.Time.Calendar(toGregorian)
import           Data.Time.Clock(utctDay,UTCTime)
import           Data.Time.Clock.POSIX(posixSecondsToUTCTime)

epochToDay :: Integer -> Day
epochToDay = utctDay . posixSecondsToUTCTime . fromIntegral

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

date :: Gen Day
date = epochToDay <$> choose (0, 1000)

cycle :: Gen Cycle
cycle = Cycle <$> choose (0, 100) <*> elements [P_D, P_W, P_M, P_Q, P_H, P_Y] <*> elements [ShortStub, LongStub]

contractTermsGen :: Gen ContractTerms
contractTermsGen = do 
    contracttype <- elements [PAM]
    sd <- date
    ied <- date
    interest <- mightbe percentage
    notional <- mightbe largeamount
    pdied <- zeroOr smallamount
    feebasis <- elements [FEB_A, FEB_N]
    feerate <- zeroOr percentage
    penaltytype <- elements [PYTP_A , PYTP_N , PYTP_I , PYTP_O]
    penaltyrate <- zeroOr percentage
    cpyrt <- zeroOr percentage
    includeendday <- elements [True, False]
    eomc <- elements [EOMC_EOM, EOMC_SD]
    bdc <- elements [BDC_NULL, BDC_SCF, BDC_SCMF, BDC_CSF, BDC_CSMF, BDC_SCP, BDC_SCMP, BDC_CSP, BDC_CSMP]
    dcc <- elements [DCC_A_AISDA, DCC_A_360, DCC_A_365, DCC_E30_360ISDA, DCC_E30_360, DCC_B_252]
    pref <- elements [PREF_Y, PREF_N]
    cntrl <- elements [CR_BUY, CR_SEL]
    scef <- elements [SE_000, SE_0N0, SE_00M, SE_0NM, SE_I00, SE_IN0, SE_I0M, SE_INM]
    scixsd <- oneOr scalingFactor
    scied <- oneOr scalingFactor
    rrsp <- zeroOr percentage
    rrmlt <- oneOr scalingFactor
    rrpf <- zeroOr percentage
    rrpc <- oneOr percentage
    rrlc <- oneOr percentage
    rrlf <- zeroOr percentage
    return ContractTerms {
        contractId     = "0"
        , contractType = Just contracttype
        , ct_IED       = ied
        , ct_SD        = sd
        , ct_MD        = Nothing
        , ct_TD        = Nothing
        , ct_PRNXT     = Nothing
        , ct_PRD       = Nothing
        , ct_CNTRL     = cntrl
        , ct_PDIED     = pdied
        , ct_NT        = notional
        , ct_PPRD      = Nothing
        , ct_PTD       = Nothing
        , ct_DCC       = dcc
        , ct_PREF      = pref
        , ct_PRF       = CS_PF
        , scfg         = ScheduleConfig {
            calendar = [] -- TODO
            , includeEndDay = includeendday
            , eomc = eomc
            , bdc = bdc
        }
        -- Penalties
        , ct_PYRT      = penaltyrate
        , ct_PYTP      = penaltytype
        , ct_cPYRT     = cpyrt
        -- Optionality
        , ct_OPCL      = Nothing
        , ct_OPANX     = Nothing
        -- Scaling:
        , ct_SCIED     = scied
        , ct_SCEF      = scef
        , ct_SCCL      = Nothing
        , ct_SCANX     = Nothing
        , ct_SCIXSD    = scixsd
        -- Rate Reset
        , ct_RRCL      = Nothing
        , ct_RRANX     = Nothing
        , ct_RRNXT     = Nothing
        , ct_RRSP      = rrsp
        , ct_RRMLT     = rrmlt
        , ct_RRPF      = rrpf
        , ct_RRPC      = rrpc
        , ct_RRLC      = rrlc
        , ct_RRLF      = rrlf
        -- Interest
        , ct_IPCED     = Nothing
        , ct_IPCL      = Nothing
        , ct_IPANX     = Nothing
        , ct_IPNR      = interest
        , ct_IPAC      = Nothing
        , ct_PRCL      = Nothing
        , ct_PRANX     = Nothing
        , ct_IPCB      = Nothing
        , ct_IPCBA     = Nothing
        , ct_IPCBCL    = Nothing
        , ct_IPCBANX   = Nothing
        -- Fee
        , ct_FECL      = Nothing
        , ct_FEANX     = Nothing
        , ct_FEAC      = Nothing
        , ct_FEB       = feebasis
        , ct_FER       = feerate
        -- enable settlement currency
        , ct_CURS      = False
        , constraints  = Nothing
    }


