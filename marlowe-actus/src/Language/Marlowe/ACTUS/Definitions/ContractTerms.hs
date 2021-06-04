{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE RecordWildCards    #-}
module Language.Marlowe.ACTUS.Definitions.ContractTerms where

import           Data.Aeson.Types (FromJSON, ToJSON)
import           Data.Maybe       (isNothing)
import           Data.Time        (Day)
import           GHC.Generics     (Generic)

 -- ContractType
data CT = PAM -- principal at maturity
        | LAM -- linear amortizer
        | NAM -- negative amortizer
        deriving stock (Show, Read, Eq, Generic) deriving anyclass (FromJSON, ToJSON)

-- ContractRole
data CR = CR_RPA -- real position asset
        | CR_RPL -- real position liability
        | CR_CLO -- role of a collateral
        | CR_CNO -- role of a close-out-netting
        | CR_COL -- role of an underlying to a collateral
        | CR_LG  -- long position
        | CR_ST  -- short position
        | CR_BUY -- protection buyer
        | CR_SEL -- protection seller
        | CR_RFL -- receive first leg
        | CR_PFL -- pay first leg
        | CR_RF  -- receive fix leg
        | CR_PF  -- pay fix leg
        deriving (Show, Read, Eq, Generic) deriving anyclass (FromJSON, ToJSON)

-- DayCountConvention
data DCC = DCC_A_AISDA     -- Actual/Actual ISDA
         | DCC_A_360       -- Actual/360
         | DCC_A_365       -- Actual/365
         | DCC_E30_360ISDA -- 30E/360 ISDA
         | DCC_E30_360     -- 30E/360
         | DCC_B_252       -- Business / 252
         deriving (Show, Read, Generic) deriving anyclass (FromJSON, ToJSON)

-- EndOfMonthConvention
data EOMC = EOMC_EOM -- end of month
          | EOMC_SD  -- same day
          deriving (Show, Read, Eq, Generic) deriving anyclass (FromJSON, ToJSON)

-- BusinessDayConvention
data BDC = BDC_NULL -- no shift
         | BDC_SCF  -- shift/calculate following
         | BDC_SCMF -- shift/calculate modified following
         | BDC_CSF  -- calculate/shift following
         | BDC_CSMF -- calculate/shift modified following
         | BDC_SCP  -- shift/calculate preceding
         | BDC_SCMP -- shift/calculate modified preceding
         | BDC_CSP  -- calculate/shift preceding
         | BDC_CSMP -- calculate/shift modified preceding
         deriving (Show, Read, Eq, Generic) deriving anyclass (FromJSON, ToJSON)

data Calendar = CLDR_MF -- monday to friday
              | CLDR_NC -- no calendar
              deriving (Show, Read, Generic) deriving anyclass (FromJSON, ToJSON)

data ScheduleConfig = ScheduleConfig
  { calendar      :: Maybe Calendar
  , includeEndDay :: Bool
  , eomc          :: Maybe EOMC
  , bdc           :: Maybe BDC
  }
  deriving stock (Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

-- ContractPerformance
data PRF = PRF_PF -- performant
         | PRF_DL -- delayed
         | PRF_DQ -- delinquent
         | PRF_DF -- default
         deriving (Show, Read, Eq, Generic) deriving anyclass (FromJSON, ToJSON)

-- FeeBasis
data FEB = FEB_A -- absolute value
         | FEB_N -- notional of underlying
         deriving (Show, Read, Eq, Generic) deriving anyclass (FromJSON, ToJSON)

 -- InterestCalculationBase
data IPCB = IPCB_NT    -- calculation base always equals to NT
          | IPCB_NTIED -- notional remains constant amount as per IED
          | IPCB_NTL   -- calculation base is notional base laged
          deriving (Show, Read, Eq, Generic) deriving anyclass (FromJSON, ToJSON)

-- ScalingEffect
data SCEF = SE_000 -- no scaling
          | SE_I00 -- only interest payments scaled
          | SE_0N0 -- only nominal payments scaled
          | SE_00M -- only maximum deferred amount scaled
          | SE_IN0 -- interest and nominal payments scaled
          | SE_0NM -- nominal and maximum deferred amount scaled
          | SE_I0M -- interest and maximum deferred amount scaled
          | SE_INM -- interest, nominal and maximum deferred amount scaled
          deriving (Show, Read, Eq, Generic) deriving anyclass (FromJSON, ToJSON)

 -- PenaltyType
data PYTP = PYTP_A -- absolute
          | PYTP_N -- nominal rate
          | PYTP_I -- current interest rate differential
          | PYTP_O -- no penalty
          deriving (Show, Read, Eq, Generic) deriving anyclass (FromJSON, ToJSON)

-- PrepaymentEffect
data PPEF = PPEF_N -- no prepayment
          | PPEF_A -- prepayment allowed, prepayment results in reduction of PRNXT while MD remains
          | PPEF_M -- prepayment allowed, prepayment results in reduction of MD while PRNXT remains
          deriving (Show, Read, Eq, Ord, Generic)
          deriving anyclass (FromJSON, ToJSON)

data CalendarType = NoCalendar
                  | MondayToFriday
                  | CustomCalendar {holidays :: [Day]}
                  deriving (Show, Generic) deriving anyclass (FromJSON, ToJSON)

 -- CyclePeriod
data Period = P_D -- day
            | P_W -- week
            | P_M -- month
            | P_Q -- quarter
            | P_H -- half year
            | P_Y -- year
            deriving (Show, Read, Eq, Ord, Generic)
            deriving anyclass (FromJSON, ToJSON)

 -- CycleStub
data Stub = ShortStub -- short last stub
          | LongStub  -- long last stub
          deriving (Show, Eq, Ord, Generic) deriving anyclass (FromJSON, ToJSON)

 -- Cycle
data Cycle = Cycle
  { n    :: Integer
  , p    :: Period
  , stub :: Stub
  }
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (FromJSON, ToJSON)

-- For applicability failures
data TermValidationError =
    Required String
    | NotApplicable String
    deriving (Eq)
instance Show TermValidationError where
    show (Required s)      = "Missing required term: " ++ s
    show (NotApplicable s) = "Term not applicable to contract: " ++ s

data Assertions = Assertions
  { context    :: AssertionContext
  , assertions :: [Assertion]
  }
  deriving stock (Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

data AssertionContext = AssertionContext
  { rrmoMin :: Double
  , rrmoMax :: Double
  }
  deriving stock (Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

data Assertion = NpvAssertionAgainstZeroRiskBond
  { zeroRiskInterest :: Double
  , expectedNpv      :: Double
  }
  deriving stock (Show, Generic)
  deriving anyclass (FromJSON, ToJSON)



data ContractTerms = ContractTerms
  { -- General
    contractId       :: String
  , contractType     :: CT
  , ct_CNTRL         :: CR

  -- Calendar
  , ct_IED           :: Maybe Day      -- Initial Exchange Date
  , ct_DCC           :: Maybe DCC      -- Day Count Convention
  , scfg             :: ScheduleConfig

  -- Contract Identification
  , ct_SD            :: Day            -- Status Date

  -- Counterparty
  , ct_PRF           :: Maybe PRF      -- Contract Performance

  -- Fees
  , ct_FECL          :: Maybe Cycle    -- Cycle Of Fee
  , ct_FEANX         :: Maybe Day      -- Cycle Anchor Date Of Fee
  , ct_FEAC          :: Maybe Double   -- Fee Accrued
  , ct_FEB           :: Maybe FEB      -- Fee Basis
  , ct_FER           :: Maybe Double   -- Fee Rate

  -- Interest
  , ct_IPANX         :: Maybe Day      -- Cycle Anchor Date Of Interest Payment
  , ct_IPCL          :: Maybe Cycle    -- Cycle Of Interest Payment
  , ct_IPAC          :: Maybe Double   -- Accrued Interest
  , ct_IPCED         :: Maybe Day      -- Capitalization End Date
  , ct_IPCBANX       :: Maybe Day      -- Cycle Anchor Date Of Interest Calculation Base
  , ct_IPCBCL        :: Maybe Cycle    -- Cycle Of Interest Calculation Base
  , ct_IPCB          :: Maybe IPCB     -- Interest Calculation Base
  , ct_IPCBA         :: Maybe Double   -- Interest Calculation Base Amount
  , ct_IPNR          :: Maybe Double   -- Nominal Interest Rate

  -- Notional Principal
  , ct_NT            :: Maybe Double   -- Notional Principal
  , ct_PDIED         :: Maybe Double   -- Premium Discount At IED
  , ct_MD            :: Maybe Day      -- Maturity Date
  , ct_PRANX         :: Maybe Day      -- Cycle Anchor Date Of Principal Redemption
  , ct_PRCL          :: Maybe Cycle    -- Cycle Of Principal Redemption
  , ct_PRNXT         :: Maybe Double   -- Next Principal Redemption Payment
  , ct_PRD           :: Maybe Day      -- Purchase Date
  , ct_PPRD          :: Maybe Double   -- Price At Purchase Date
  , ct_TD            :: Maybe Day      -- Termination Date
  , ct_PTD           :: Maybe Double   -- Price At Termination Date
  , ct_SCIED         :: Maybe Double   -- Scaling Index At Status Date
  , ct_SCANX         :: Maybe Day      -- Cycle Anchor Date Of Scaling Index
  , ct_SCCL          :: Maybe Cycle    -- Cycle Of Scaling Index
  , ct_SCEF          :: Maybe SCEF     -- Scaling Effect
  , ct_SCCDD         :: Maybe Double   -- Scaling Index At Contract Deal Date

  -- Optionality
  , ct_OPCL          :: Maybe Cycle    -- Cycle Of Optionality
  , ct_OPANX         :: Maybe Day      -- Cycle Anchor Date Of Optionality
  , ct_PYRT          :: Maybe Double   -- Penalty Rate
  , ct_PYTP          :: Maybe PYTP     -- Penalty Type
  , ct_PPEF          :: Maybe PPEF     -- Prepayment Effect
  , ct_cPYRT         :: Double

  -- Rate Reset
  , ct_RRCL          :: Maybe Cycle    -- Cycle Of Rate Reset
  , ct_RRANX         :: Maybe Day      -- Cycle Anchor Date Of Rate Reset
  , ct_RRNXT         :: Maybe Double   -- Next Reset Rate
  , ct_RRSP          :: Maybe Double   -- Rate Spread
  , ct_RRMLT         :: Maybe Double   -- Rate Multiplier
  , ct_RRPF          :: Maybe Double   -- Period Floor
  , ct_RRPC          :: Maybe Double   -- Period Cap
  , ct_RRLC          :: Maybe Double   -- Life Cap
  , ct_RRLF          :: Maybe Double   -- Life Floor

  -- enable settlement currency
  , ct_CURS          :: Bool
  , constraints      :: Maybe Assertions
  , collateralAmount :: Integer
  }
  deriving stock (Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

defaultPDIED :: Double
defaultPDIED = 0

defaultPYRT :: Double
defaultPYRT = 0

defaultRRSP :: Double
defaultRRSP = 0

defaultRRMLT :: Double
defaultRRMLT = 1.0

setDefaultContractTermValues :: ContractTerms -> ContractTerms
setDefaultContractTermValues ct@ContractTerms{..} =
  let
      ScheduleConfig{..} = scfg

      eomc'     | isNothing eomc     = Just EOMC_SD
                | otherwise          = eomc

      bdc'      | isNothing bdc      = Just BDC_SCF
                | otherwise          = bdc

      calendar' | isNothing calendar = Just CLDR_NC
                | otherwise          = calendar

      ct_PRF'   | isNothing ct_PRF   = Just PRF_PF
                | otherwise          = ct_PRF

      ct_IPCB'  | isNothing ct_IPCB  = Just IPCB_NT
                | otherwise          = ct_IPCB

      ct_PDIED' | isNothing ct_PDIED = Just defaultPDIED
                | otherwise          = ct_PDIED

      ct_SCEF'  | isNothing ct_SCEF  = Just SE_000
                | otherwise          = ct_SCEF

      ct_PYRT'  | isNothing ct_PYRT  = Just defaultPYRT
                | otherwise          = ct_PYRT

      ct_PYTP'  | isNothing ct_PYTP  = Just PYTP_O
                | otherwise          = ct_PYTP

      ct_PPEF'  | isNothing ct_PPEF  = Just PPEF_N
                | otherwise          = ct_PPEF

      ct_RRSP'  | isNothing ct_RRSP  = Just defaultRRSP
                | otherwise          = ct_RRSP

      ct_RRMLT' | isNothing ct_RRMLT = Just defaultRRMLT
                | otherwise          = ct_RRMLT
  in ct {
    scfg     = scfg { eomc = eomc', bdc = bdc', calendar = calendar' },
    ct_PRF   = ct_PRF',
    ct_IPCB  = ct_IPCB',
    ct_PDIED = ct_PDIED',
    ct_SCEF  = ct_SCEF',
    ct_PYRT  = ct_PYRT',
    ct_PYTP  = ct_PYTP',
    ct_PPEF  = ct_PPEF',
    ct_RRSP  = ct_RRSP',
    ct_RRMLT = ct_RRMLT'
  }
