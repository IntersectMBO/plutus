{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
module Language.Marlowe.ACTUS.Definitions.ContractTerms where

import           Data.Aeson.Types (FromJSON, ToJSON)
import           Data.Time        (Day)
import           GHC.Generics     (Generic)

data PYTP = PYTP_A | PYTP_N | PYTP_I | PYTP_O deriving (Show, Eq, Generic) deriving anyclass (FromJSON, ToJSON)

data FEB = FEB_A | FEB_N deriving (Show, Eq, Generic) deriving anyclass (FromJSON, ToJSON)

data IPCB = IPCB_NT | IPCB_NTIED | IPCB_NTL deriving (Show, Eq, Generic) deriving anyclass (FromJSON, ToJSON)

data EOMC = EOMC_EOM
          | EOMC_SD deriving (Show, Eq, Generic) deriving anyclass (FromJSON, ToJSON)

data BDC =  BDC_NULL
          | BDC_SCF
          | BDC_SCMF
          | BDC_CSF
          | BDC_CSMF
          | BDC_SCP
          | BDC_SCMP
          | BDC_CSP
          | BDC_CSMP deriving (Show, Eq, Generic) deriving anyclass (FromJSON, ToJSON)

data DCC =  DCC_A_AISDA
          | DCC_A_360
          | DCC_A_365
          | DCC_E30_360ISDA
          | DCC_E30_360
          | DCC_B_252 deriving (Show, Generic) deriving anyclass (FromJSON, ToJSON)

data CalendarType = NoCalendar | MondayToFriday | CustomCalendar {holidays :: [Day]} deriving (Show, Generic) deriving anyclass (FromJSON, ToJSON)

data ContractRole = CR_RPA -- Real position asset
                  | CR_RPL -- Real position liability
                  | CR_CLO -- Role of a collateral
                  | CR_CNO -- Role of a close-out-netting
                  | CR_COL -- Role of an underlying to a collateral
                  | CR_LG  -- Long position
                  | CR_ST  -- Short position
                  | CR_BUY -- Protection buyer
                  | CR_SEL -- Protection seller
                  | CR_RFL -- Receive first leg
                  | CR_PFL -- Pay first leg
                  | CR_RF  -- Receive fix leg
                  | CR_PF  -- Pay fix leg
                  deriving (Show, Eq, Generic) deriving anyclass (FromJSON, ToJSON)
--ScalingEffect
data SCEF =  SE_000
                    | SE_0N0
                    | SE_00M
                    | SE_0NM
                    | SE_I00
                    | SE_IN0
                    | SE_I0M
                    | SE_INM deriving (Show, Eq, Generic) deriving anyclass (FromJSON, ToJSON)

--InterestCalculationBase
data ICB = ICB_NT | ICB_NTIED | ICB_NTL deriving (Show, Eq, Generic) deriving anyclass (FromJSON, ToJSON)

--FeeBasis
data FB = FB_A | FB_N deriving (Show, Eq, Generic) deriving anyclass (FromJSON, ToJSON)

--PenaltyType
data PT = PT_O | PT_A | PT_N | PT_I deriving (Show, Eq, Generic) deriving anyclass (FromJSON, ToJSON)

--PrepaymentEffect
data PE = PE_N | PE_A | PE_M deriving (Show, Eq, Generic) deriving anyclass (FromJSON, ToJSON)

data Period = P_D
            | P_W
            | P_M
            | P_Q
            | P_H
            | P_Y
            deriving (Show, Eq, Ord, Generic)
             deriving anyclass (FromJSON, ToJSON)

data PREF = PREF_N | PREF_Y
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (FromJSON, ToJSON)

data ContractStatus = CS_PF -- performant
                    | CS_DL -- delayed
                    | CS_DQ -- delinquent
                    | CS_DF -- default
                    deriving (Show, Eq, Generic) deriving anyclass (FromJSON, ToJSON)

data Stub = ShortStub | LongStub deriving (Show, Eq, Ord, Generic) deriving anyclass (FromJSON, ToJSON)

data Cycle = Cycle
  { n    :: Integer
  , p    :: Period
  , stub :: Stub
  } deriving (Show, Eq, Ord, Generic)
  deriving anyclass (FromJSON, ToJSON)

-- For applicability failures
data TermValidationError =
    Required String
    | NotApplicable String
    deriving (Eq)
instance Show TermValidationError where
    show (Required s) = "Missing required term: " ++ s
    show (NotApplicable s) = "Term not applicable to contract: " ++ s

data ScheduleConfig = ScheduleConfig
  {
    calendar      :: [Day]
  , includeEndDay :: Bool
  , eomc          :: EOMC
  , bdc           :: BDC
  }   deriving stock (Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

data ContractType = PAM | LAM   deriving stock (Show, Eq, Generic) deriving anyclass (FromJSON, ToJSON)


data Assertions = Assertions
  {
    context      :: AssertionContext
    , assertions :: [Assertion]
  } deriving stock (Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

data AssertionContext = AssertionContext
  {
    rrmoMin   :: Double
    , rrmoMax :: Double
  } deriving stock (Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

data Assertion = NpvAssertionAgainstZeroRiskBond
  {
    zeroRiskInterest :: Double
    , expectedNpv    :: Double
  } deriving stock (Show, Generic)
  deriving anyclass (FromJSON, ToJSON)



data ContractTerms = ContractTerms {
  contractId     :: String
  , contractType :: Maybe ContractType
  , ct_IED       :: Day -- Initial Exchange Date
  , ct_SD        :: Day -- start date
  , ct_MD        :: Maybe Day -- maturity date
  , ct_TD        :: Maybe Day -- termination date
  , ct_PRNXT     :: Maybe Double -- periodic payment amount
  , ct_PRD       :: Maybe Day -- purchase date
  , ct_CNTRL     :: ContractRole
  , ct_PDIED     :: Double -- Premium / Discount At IED
  , ct_NT        :: Maybe Double -- Notional
  , ct_PPRD      :: Maybe Double -- Price At Purchase Date
  , ct_PTD       :: Maybe Double -- Price At Termination Date
  , ct_DCC       :: DCC -- Date Count Convention
  , ct_PREF      :: PREF -- allow PP
  , ct_PRF       :: ContractStatus
  , scfg         :: ScheduleConfig
  -- Penalties
  , ct_PYRT      :: Double -- Penalty Rate
  , ct_PYTP      :: PYTP -- Penalty Pype
  , ct_cPYRT     :: Double
  -- Optionality
  , ct_OPCL      :: Maybe Cycle
  , ct_OPANX     :: Maybe Day
  -- Scaling:
  , ct_SCIED     :: Double
  , ct_SCEF      :: SCEF
  , ct_SCCL      :: Maybe Cycle
  , ct_SCANX     :: Maybe Day
  , ct_SCIXSD    :: Double
  -- Rate Reset
  , ct_RRCL      :: Maybe Cycle
  , ct_RRANX     :: Maybe Day
  , ct_RRNXT     :: Maybe Double -- next reset date
  , ct_RRSP      :: Double
  , ct_RRMLT     :: Double
  , ct_RRPF      :: Double
  , ct_RRPC      :: Double
  , ct_RRLC      :: Double
  , ct_RRLF      :: Double
  -- Interest
  , ct_IPCED     :: Maybe Day
  , ct_IPCL      :: Maybe Cycle
  , ct_IPANX     :: Maybe Day
  , ct_IPNR      :: Maybe Double
  , ct_IPAC      :: Maybe Double
  , ct_PRCL      :: Maybe Cycle
  , ct_PRANX     :: Maybe Day
  , ct_IPCB      :: Maybe IPCB   -- Interest calc base
  , ct_IPCBA     :: Maybe Double -- Amount used for interest calculation
  , ct_IPCBCL    :: Maybe Cycle  -- Cycle of interest calculation base
  , ct_IPCBANX    :: Maybe Day   -- Anchor of interest calc base cycle
  -- Fee
  , ct_FECL      :: Maybe Cycle
  , ct_FEANX     :: Maybe Day
  , ct_FEAC      :: Maybe Double
  , ct_FEB       :: FEB  -- fee basis
  , ct_FER       :: Double -- fee rate
  -- enable settlement currency
  , ct_CURS      :: Bool
  , constraints  :: Maybe Assertions
  }
  deriving stock (Show, Generic)
  deriving anyclass (FromJSON, ToJSON)
