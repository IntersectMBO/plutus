{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
module Language.Marlowe.ACTUS.Definitions.ContractTerms where

import Data.Time ( Day )
import Language.Marlowe.ACTUS.Definitions.ContractState ( ContractStatus )
import qualified Data.Aeson                 as JSON
import qualified Data.Aeson.Extras          as JSON
import           Data.Aeson.Types           hiding (Error, Value)
import           GHC.Generics

type Calendar = [Day]

data PYTP = PYTP_A | PYTP_N | PYTP_I | PYTP_O deriving (Show, Eq, Generic) deriving anyclass (FromJSON, ToJSON)

data FEB = FEB_A | FEB_N deriving (Show, Eq, Generic) deriving anyclass (FromJSON, ToJSON)

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

data SCEF =  SE_000 --ScalingEffect
                    | SE_0N0
                    | SE_00M
                    | SE_0NM
                    | SE_I00
                    | SE_IN0
                    | SE_I0M
                    | SE_INM deriving (Show, Eq, Generic) deriving anyclass (FromJSON, ToJSON)

data ICB = ICB_NT | ICB_NTIED | ICB_NTL deriving (Show, Eq, Generic) deriving anyclass (FromJSON, ToJSON)--InterestCalculationBase

data FB = FB_A | FB_N deriving (Show, Eq, Generic) deriving anyclass (FromJSON, ToJSON)--FeeBasis

data PT = PT_O | PT_A | PT_N | PT_I deriving (Show, Eq, Generic) deriving anyclass (FromJSON, ToJSON) --PenaltyType

data PE = PE_N | PE_A | PE_M deriving (Show, Eq, Generic) deriving anyclass (FromJSON, ToJSON)--PrepaymentEffect

data Period = P_D -- Day
            | P_W -- Week
            | P_M -- Month
            | P_Q -- Quarter
            | P_H -- Half Year
            | P_Y -- Year
            deriving (Show, Eq, Ord, Generic)
             deriving anyclass (FromJSON, ToJSON)

data PREF = PREF_N | PREF_Y 
  deriving (Show, Eq, Ord, Generic)
  deriving anyclass (FromJSON, ToJSON)
-- wether PP is allowed

data Stub = ShortStub | LongStub deriving (Show, Eq, Ord, Generic) deriving anyclass (FromJSON, ToJSON)

data Cycle = Cycle
  { n :: Integer
  , p :: Period
  , stub :: Stub
  } deriving (Show, Eq, Ord, Generic)
  deriving anyclass (FromJSON, ToJSON)

data ScheduleConfig = ScheduleConfig
  {
    calendar :: Calendar
  , includeEndDay :: Bool
  , eomc :: EOMC
  , bdc :: BDC
  }   deriving stock (Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

data ContractType = PAM | LAM   deriving stock (Show, Generic) deriving anyclass (FromJSON, ToJSON)

data ContractTerms = ContractTerms {
  contractId :: String
  , contractType :: ContractType
  , _IED :: Day -- Initial Exchange Date
  , _SD :: Day -- start date
  , _MD :: Day -- maturity date
  , _TD :: Day -- termination date
  , _PRD :: Day -- purchase date
  , _CNTRL :: ContractRole
  , _PDIED :: Double -- Premium / Discount At IED
  , _NT :: Double -- Notional
  , _PPRD :: Double -- Price At Purchase Date
  , _PTD :: Double -- Price At Termination Date
  , _DCC :: DCC -- Date Count Convention
  , _PREF :: PREF -- allow PP
  , _PRF :: ContractStatus
  , scfg :: ScheduleConfig
  -- Penalties
  , _PYRT :: Double -- Penalty Rate
  , _PYTP :: PYTP -- Penalty Pype
  , _cPYRT :: Double
  -- Optionality
  , _OPCL :: Maybe Cycle
  , _OPANX :: Maybe Day
  -- Scaling:
  , _SCIED :: Double
  , _SCEF :: SCEF
  , _SCCL :: Maybe Cycle
  , _SCANX :: Maybe Day
  , _SCIXSD :: Double
  -- Rate Reset
  , _RRCL :: Maybe Cycle
  , _RRANX :: Maybe Day
  , _RRNXT :: Maybe Double -- next reset date
  , _RRSP :: Double
  , _RRMLT :: Double
  , _RRPF :: Double
  , _RRPC :: Double
  , _RRLC :: Double
  , _RRLF :: Double
  -- Interest
  , _IPCED :: Maybe Day
  , _IPCL :: Maybe Cycle
  , _IPANX :: Maybe Day
  , _IPNR :: Maybe Double
  , _IPAC :: Maybe Double
  -- Fee
  , _FECL :: Maybe Cycle
  , _FEANX :: Maybe Day
  , _FEAC :: Maybe Double
  , _FEB :: FEB  -- fee basis
  , _FER :: Double -- fee rate
  }
  deriving stock (Show,Generic)
  deriving anyclass (FromJSON, ToJSON)
