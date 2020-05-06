module Language.Marlowe.ACTUS.ContractTerms where

import Data.Map (Map)
import Data.Bool

import Data.Time
import Language.Marlowe.ACTUS.ContractState

data PYTP = PYTP_A | PYTP_N | PYTP_I | PYTP_O

data FEB = FEB_A | FEB_N deriving (Show, Eq)

data EOMC = EOMC_EOM
          | EOMC_SD deriving (Show, Eq)

data BDC =  BDC_NULL
          | BDC_SCF
          | BDC_SCMF
          | BDC_CSF
          | BDC_CSMF
          | BDC_SCP
          | BDC_SCMP
          | BDC_CSP
          | BDC_CSMP deriving (Show, Eq)

data DCC =  DCC_A_AISDA
          | DCC_A_360
          | DCC_A_365
          | DCC_E30_360ISDA
          | DCC_E30_360
          | DCC_B_252 deriving (Show)

{- B-function -}
type Calendar = Day -> Bool

data CalendarType = NoCalendar | MondayToFriday | CustomCalendar {holidays :: [Day]} deriving (Show)

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
                  deriving (Show, Eq)

data SCEF =  SE_000 --ScalingEffect
                    | SE_0N0
                    | SE_00M
                    | SE_0NM
                    | SE_I00
                    | SE_IN0
                    | SE_I0M
                    | SE_INM deriving (Show, Eq)

data ICB = ICB_NT | ICB_NTIED | ICB_NTL deriving (Show, Eq) --InterestCalculationBase

data FB = FB_A | FB_N deriving (Show, Eq) --FeeBasis

data PT = PT_O | PT_A | PT_N | PT_I deriving (Show, Eq) --PenaltyType

data PE = PE_N | PE_A | PE_M deriving (Show, Eq) --PrepaymentEffect

data Period = P_D -- Day
            | P_W -- Week
            | P_M -- Month
            | P_Q -- Quarter
            | P_H -- Half Year
            | P_Y -- Year
            deriving (Show, Eq, Ord)

data PREF = PREF_N | PREF_Y -- wether PP is allowed

data Stub = ShortStub | LongStub deriving (Show, Eq, Ord)

data Cycle = Cycle
  { n :: Integer
  , p :: Period
  , stub :: Stub
  } deriving (Show, Eq, Ord)

data ScheduleConfig = ScheduleConfig
  {
    calendar :: Calendar
  , includeEndDay :: Bool
  , eomc :: EOMC
  , bdc :: BDC
  }

-- all contract terms in a composite contract
type ContractTermsContext = Map String ContractTerms

data ContractTerms = PamContractTerms { 
  contractId :: String
  , _SD :: Day
  , _MD :: Day
  , _TD :: Day
  , _PRD :: Day
  , _CNTRL :: ContractRole
  , _PDIED :: Double
  , _NT :: Double
  , _PYRT :: Double
  , _PYTP :: PYTP
  , _FEB :: FEB
  , _FER :: Double
  , _PPRD :: Double
  , _PTD :: Double
  , _cPYRT :: Double
  , _DCC :: DCC
  , _IED :: Day
  , _PREF :: PREF
  , _OPCL :: Maybe Cycle
  , _OPANX :: Maybe Day
  , _SCIED :: Double
  , _SCEF :: SCEF
  , _SCCL :: Maybe Cycle
  , _SCANX :: Maybe Day
  , _SCIXSD :: Double
  , _RRCL :: Maybe Cycle
  , _RRANX :: Maybe Day
  , _RRNXT :: Maybe Double -- next reset date
  , _RRSP :: Double
  , _RRMLT :: Double
  , _RRPF :: Double
  , _RRPC :: Double
  , _RRLC :: Double
  , _RRLF :: Double
  , _IPCED :: Maybe Day
  , _IPCL :: Maybe Cycle
  , _IPANX :: Maybe Day
  , _IPNR :: Maybe Double
  , _IPAC :: Maybe Double
  , _FECL :: Maybe Cycle
  , _FEANX :: Maybe Day
  , _FEAC :: Maybe Double
  , _PRF :: ContractStatus
  , scfg :: ScheduleConfig
  } | LamContractTerms { 
    _MD :: Day
  , _CNTRL :: ContractRole
  }
