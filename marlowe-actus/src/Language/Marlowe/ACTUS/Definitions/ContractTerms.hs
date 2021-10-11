{-# LANGUAGE DeriveAnyClass       #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DerivingStrategies   #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE RecordWildCards      #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Language.Marlowe.ACTUS.Definitions.ContractTerms where

import           Data.Aeson.Types (FromJSON, ToJSON)
import           Data.Maybe       (fromMaybe)
import           Data.Time        (Day, LocalTime)
import           GHC.Generics     (Generic)
import qualified Language.Marlowe as Marlowe (Observation, Value)

-- |ContractType
data CT = PAM -- ^ Principal at maturity
        | LAM -- ^ Linear amortizer
        | NAM -- ^ Negative amortizer
        | ANN -- ^ Annuity
        | STK -- ^ Stock
        | OPTNS -- ^ Option
        | FUTUR -- ^ Future
        deriving stock (Show, Read, Eq, Generic)
        deriving anyclass (FromJSON, ToJSON)

-- |ContractRole
data CR = CR_RPA -- ^ Real position asset
        | CR_RPL -- ^ Real position liability
        | CR_CLO -- ^ Role of a collateral
        | CR_CNO -- ^ Role of a close-out-netting
        | CR_COL -- ^ Role of an underlying to a collateral
        | CR_LG  -- ^ Long position
        | CR_ST  -- ^ Short position
        | CR_BUY -- ^ Protection buyer
        | CR_SEL -- ^ Protection seller
        | CR_RFL -- ^ Receive first leg
        | CR_PFL -- ^ Pay first leg
        | CR_RF  -- ^ Receive fix leg
        | CR_PF  -- ^ Pay fix leg
        deriving stock (Show, Read, Eq, Generic)
        deriving anyclass (FromJSON, ToJSON)

-- |DayCountConvention
data DCC = DCC_A_AISDA     -- ^ Actual/Actual ISDA
         | DCC_A_360       -- ^ Actual/360
         | DCC_A_365       -- ^ Actual/365
         | DCC_E30_360ISDA -- ^ 30E/360 ISDA
         | DCC_E30_360     -- ^ 30E/360
         | DCC_B_252       -- ^ Business / 252
         deriving stock (Show, Read, Eq, Generic)
         deriving anyclass (FromJSON, ToJSON)

-- |EndOfMonthConvention
data EOMC = EOMC_EOM -- ^ End of month
          | EOMC_SD  -- ^ Same day
          deriving stock (Show, Read, Eq, Generic)
          deriving anyclass (FromJSON, ToJSON)

-- |BusinessDayConvention
data BDC = BDC_NULL -- ^ No shift
         | BDC_SCF  -- ^ Shift/calculate following
         | BDC_SCMF -- ^ Shift/calculate modified following
         | BDC_CSF  -- ^ Calculate/shift following
         | BDC_CSMF -- ^ Calculate/shift modified following
         | BDC_SCP  -- ^ Shift/calculate preceding
         | BDC_SCMP -- ^ Shift/calculate modified preceding
         | BDC_CSP  -- ^ Calculate/shift preceding
         | BDC_CSMP -- ^ Calculate/shift modified preceding
         deriving stock (Show, Read, Eq, Generic)
         deriving anyclass (FromJSON, ToJSON)

data Calendar = CLDR_MF -- ^ Monday to Friday
              | CLDR_NC -- ^ No calendar
              deriving stock (Show, Read, Eq, Generic)
              deriving anyclass (FromJSON, ToJSON)

data ScheduleConfig = ScheduleConfig
  { calendar :: Maybe Calendar
  , eomc     :: Maybe EOMC
  , bdc      :: Maybe BDC
  }
  deriving stock (Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

-- |ContractPerformance
data PRF = PRF_PF -- ^ Performant
         | PRF_DL -- ^ Delayed
         | PRF_DQ -- ^ Delinquent
         | PRF_DF -- ^ Default
         deriving stock (Show, Read, Eq, Generic)
         deriving anyclass (FromJSON, ToJSON)

-- |FeeBasis
data FEB = FEB_A -- ^ Absolute value
         | FEB_N -- ^ Notional of underlying
         deriving stock (Show, Read, Eq, Generic)
         deriving anyclass (FromJSON, ToJSON)

-- |InterestCalculationBase
data IPCB = IPCB_NT    -- ^ Calculation base always equals to NT
          | IPCB_NTIED -- ^ Notional remains constant amount as per IED
          | IPCB_NTL   -- ^ Calculation base is notional base laged
          deriving stock (Show, Read, Eq, Generic)
          deriving anyclass (FromJSON, ToJSON)

-- |ScalingEffect
data SCEF = SE_000 -- ^ No scaling
          | SE_I00 -- ^ Only interest payments scaled
          | SE_0N0 -- ^ Only nominal payments scaled
          | SE_00M -- ^ Only maximum deferred amount scaled
          | SE_IN0 -- ^ Interest and nominal payments scaled
          | SE_0NM -- ^ Nominal and maximum deferred amount scaled
          | SE_I0M -- ^ Interest and maximum deferred amount scaled
          | SE_INM -- ^ Interest, nominal and maximum deferred amount scaled
          deriving stock (Show, Read, Eq, Generic)
          deriving anyclass (FromJSON, ToJSON)

-- |PenaltyType
data PYTP = PYTP_A -- ^ Absolute
          | PYTP_N -- ^ Nominal rate
          | PYTP_I -- ^ Current interest rate differential
          | PYTP_O -- ^ No penalty
          deriving stock (Show, Read, Eq, Generic)
          deriving anyclass (FromJSON, ToJSON)

-- |Option Type
data OPTP = OPTP_C  -- ^ Call Option
          | OPTP_P  -- ^ Put Option
          | OPTP_CP -- ^ Call-Put Option
          deriving stock (Show, Read, Eq, Generic)
          deriving anyclass (FromJSON, ToJSON)

-- |Option Exercise Type
data OPXT = OPXT_E -- ^ European
          | OPXT_B -- ^ Bermudan
          | OPXT_A -- ^ American
          deriving stock (Show, Read, Eq, Generic)
          deriving anyclass (FromJSON, ToJSON)

-- |Settlement
data DS = DS_S -- ^ Cash Settlement
        | DS_D -- ^ Physical Settlement
          deriving stock (Show, Read, Eq, Generic)
          deriving anyclass (FromJSON, ToJSON)

-- |PrepaymentEffect
data PPEF = PPEF_N -- ^ No prepayment
          | PPEF_A -- ^ Prepayment allowed, prepayment results in reduction of PRNXT while MD remains
          | PPEF_M -- ^ Prepayment allowed, prepayment results in reduction of MD while PRNXT remains
          deriving stock (Show, Read, Eq, Ord, Generic)
          deriving anyclass (FromJSON, ToJSON)

data CalendarType = NoCalendar
                  | MondayToFriday
                  | CustomCalendar {holidays :: [Day]}
                  deriving stock (Show, Generic)
                  deriving anyclass (FromJSON, ToJSON)

-- |CyclePeriod
data Period = P_D -- ^ Day
            | P_W -- ^ Week
            | P_M -- ^ Month
            | P_Q -- ^ Quarter
            | P_H -- ^ Half year
            | P_Y -- ^ Year
            deriving stock (Show, Read, Eq, Ord, Generic)
            deriving anyclass (FromJSON, ToJSON)

-- |CycleStub
data Stub = ShortStub -- ^ Short last stub
          | LongStub  -- ^ Long last stub
          deriving stock (Show, Eq, Ord, Generic)
          deriving anyclass (FromJSON, ToJSON)

-- |Cycle
data Cycle = Cycle
  { n             :: Integer
  , p             :: Period
  , stub          :: Stub
  , includeEndDay :: Bool
  }
  deriving stock (Show, Eq, Ord, Generic)
  deriving anyclass (FromJSON, ToJSON)

-- For applicability failures
data TermValidationError =
    Required String
    | NotApplicable String
    deriving stock (Eq)
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

-- |Reference type
data ReferenceType = CNT
                   | CID
                   | MOC
                   | EID
                   | CST
  deriving stock (Eq, Show, Read, Generic)
  deriving anyclass (FromJSON, ToJSON)

-- |Reference role
data ReferenceRole = UDL
  deriving stock (Eq, Read, Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

-- |Market object code
type MarketObjectCode = String

-- |Contract structure
data ContractStructure = ContractStructure
  {
    marketObjectCode :: MarketObjectCode
  , referenceType    :: ReferenceType
  , referenceRole    :: ReferenceRole
  }
  deriving stock (Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

{-| ACTUS contract terms and attributes are defined in
    https://github.com/actusfrf/actus-dictionary/blob/master/actus-dictionary-terms.json
-}
data ContractTermsPoly a b = ContractTermsPoly
  { -- General
    contractId        :: String
  , contractType      :: CT
  , contractStructure :: [ContractStructure]
  , ct_CNTRL          :: CR
  , ct_CURS           :: Maybe String

  -- Calendar
  , ct_IED            :: Maybe b         -- ^ Initial Exchange Date
  , ct_DCC            :: Maybe DCC       -- ^ Day Count Convention
  , scfg              :: ScheduleConfig

  -- Contract Identification
  , ct_SD             :: b               -- ^ Status Date

  -- Counterparty
  , ct_PRF            :: Maybe PRF       -- ^ Contract Performance

  -- Fees
  , ct_FECL           :: Maybe Cycle     -- ^ Cycle Of Fee
  , ct_FEANX          :: Maybe b         -- ^ Cycle Anchor Date Of Fee
  , ct_FEAC           :: Maybe a         -- ^ Fee Accrued
  , ct_FEB            :: Maybe FEB       -- ^ Fee Basis
  , ct_FER            :: Maybe a         -- ^ Fee Rate

  -- Interest
  , ct_IPANX          :: Maybe b         -- ^ Cycle Anchor Date Of Interest Payment
  , ct_IPCL           :: Maybe Cycle     -- ^ Cycle Of Interest Payment
  , ct_IPAC           :: Maybe a         -- ^ Accrued Interest
  , ct_IPCED          :: Maybe b         -- ^ Capitalization End Date
  , ct_IPCBANX        :: Maybe b         -- ^ Cycle Anchor Date Of Interest Calculation Base
  , ct_IPCBCL         :: Maybe Cycle     -- ^ Cycle Of Interest Calculation Base
  , ct_IPCB           :: Maybe IPCB      -- ^ Interest Calculation Base
  , ct_IPCBA          :: Maybe a         -- ^ Interest Calculation Base Amount
  , ct_IPNR           :: Maybe a         -- ^ Nominal Interest Rate
  , ct_SCIP           :: Maybe a         -- ^ Interest Scaling Multiplier

  -- Dates
  , ct_MD             :: Maybe b         -- ^ Maturity Date
  , ct_AD             :: Maybe b         -- ^ Amortization Date
  , ct_XD             :: Maybe b         -- ^ Exercise Date
  -- , ct_STD                   :: Maybe b         -- ^ Settlement Date

  -- Notional Principal
  , ct_NT             :: Maybe a         -- ^ Notional Principal
  , ct_PDIED          :: Maybe a         -- ^ Premium Discount At IED
  , ct_PRANX          :: Maybe b         -- ^ Cycle Anchor Date Of Principal Redemption
  , ct_PRCL           :: Maybe Cycle     -- ^ Cycle Of Principal Redemption
  , ct_PRNXT          :: Maybe a         -- ^ Next Principal Redemption Payment
  , ct_PRD            :: Maybe b         -- ^ Purchase Date
  , ct_PPRD           :: Maybe a         -- ^ Price At Purchase Date
  , ct_TD             :: Maybe b         -- ^ Termination Date
  , ct_PTD            :: Maybe a         -- ^ Price At Termination Date

  -- Scaling Index
  , ct_SCIED          :: Maybe a         -- ^ Scaling Index At Status Date
  , ct_SCANX          :: Maybe b         -- ^ Cycle Anchor Date Of Scaling Index
  , ct_SCCL           :: Maybe Cycle     -- ^ Cycle Of Scaling Index
  , ct_SCEF           :: Maybe SCEF      -- ^ Scaling Effect
  , ct_SCCDD          :: Maybe a         -- ^ Scaling Index At Contract Deal Date
  , ct_SCMO           :: Maybe String    -- ^ Market Object Code Of Scaling Index
  , ct_SCNT           :: Maybe a         -- ^ Notional Scaling Multiplier

  -- Optionality
  , ct_OPCL           :: Maybe Cycle     -- ^ Cycle Of Optionality
  , ct_OPANX          :: Maybe b         -- ^ Cycle Anchor Date Of Optionality
  , ct_OPTP           :: Maybe OPTP      -- ^ Option Type
  , ct_OPS1           :: Maybe a         -- ^ Option Strike 1
  , ct_OPXT           :: Maybe OPXT      -- ^ Option Exercise Type

  -- Settlement
  , ct_STP            :: Maybe Cycle     -- ^ Settlement Period
  , ct_DS             :: Maybe DS        -- ^ Delivery Settlement
  , ct_XA             :: Maybe a         -- ^ Exercise Amount

  -- Penalty
  , ct_PYRT           :: Maybe a         -- ^ Penalty Rate
  , ct_PYTP           :: Maybe PYTP      -- ^ Penalty Type
  , ct_PPEF           :: Maybe PPEF      -- ^ Prepayment Effect

  -- Rate Reset
  , ct_RRCL           :: Maybe Cycle     -- ^ Cycle Of Rate Reset
  , ct_RRANX          :: Maybe b         -- ^ Cycle Anchor Date Of Rate Reset
  , ct_RRNXT          :: Maybe a         -- ^ Next Reset Rate
  , ct_RRSP           :: Maybe a         -- ^ Rate Spread
  , ct_RRMLT          :: Maybe a         -- ^ Rate Multiplier
  , ct_RRPF           :: Maybe a         -- ^ Period Floor
  , ct_RRPC           :: Maybe a         -- ^ Period Cap
  , ct_RRLC           :: Maybe a         -- ^ Life Cap
  , ct_RRLF           :: Maybe a         -- ^ Life Floor
  , ct_RRMO           :: Maybe String    -- ^ Market Object Code Of Rate Reset

  -- Dividend
  , ct_DVCL           :: Maybe Cycle     -- ^ Cycle Of Dividend
  , ct_DVANX          :: Maybe b         -- ^ Cycle Anchor Date Of Dividend
  , ct_DVNP           :: Maybe a         -- ^ Next Dividend Payment Amount

  -- enable settlement currency
  , enableSettlement  :: Bool
  , constraints       :: Maybe Assertions
  , collateralAmount  :: Integer
  }
  deriving stock (Show, Generic)
  deriving anyclass (FromJSON, ToJSON)

  {- TODO: SCP-2881

instance FromJSON ContractTerms where
  parseJSON (Object v) =
    ContractTermsPoly
      <$> v .:  "contractId"
      <*> v .:  "contractType"
      <*> v .:? "contractStructure"
      <*> v .:  "contractRole"
      <*> v .:? "settlementCurrency"
      <*> v .:? "initialExchangeDate"
      <*> v .:? "dayCountConvention"
      ...
 -}

type ContractTerms = ContractTermsPoly Double LocalTime
type ContractTermsMarlowe = ContractTermsPoly (Marlowe.Value Marlowe.Observation) (Marlowe.Value Marlowe.Observation)

setDefaultContractTermValues :: ContractTerms -> ContractTerms
setDefaultContractTermValues ct@ContractTermsPoly{..} =
  let ScheduleConfig{..} = scfg in
    ct {
      scfg     = scfg
        { eomc = applyDefault EOMC_SD eomc
        , bdc = applyDefault BDC_NULL bdc
        , calendar = applyDefault CLDR_NC calendar
        }
    , ct_PRF   = applyDefault PRF_PF ct_PRF
    , ct_IPCB  = applyDefault IPCB_NT ct_IPCB
    , ct_PDIED = applyDefault 0.0 ct_PDIED
    , ct_SCEF  = applyDefault SE_000 ct_SCEF
    , ct_PYRT  = applyDefault 0.0 ct_PYRT
    , ct_PYTP  = applyDefault PYTP_O ct_PYTP
    , ct_PPEF  = applyDefault PPEF_N ct_PPEF
    , ct_RRSP  = applyDefault 0.0 ct_RRSP
    , ct_RRMLT = applyDefault 1.0 ct_RRMLT
    , ct_FEAC  = applyDefault 0.0 ct_FEAC
    , ct_FER   = applyDefault 0.0 ct_FER
    , ct_IPAC  = applyDefault 0.0 ct_IPAC
    , ct_IPNR  = applyDefault 0.0 ct_IPNR
    , ct_PPRD  = applyDefault 0.0 ct_PPRD
    , ct_PTD   = applyDefault 0.0 ct_PTD
    , ct_SCCDD = applyDefault 0.0 ct_SCCDD
    , ct_RRPF  = applyDefault (-infinity) ct_RRPF
    , ct_RRPC  = applyDefault infinity ct_RRPC
    , ct_RRLC  = applyDefault infinity ct_RRLC
    , ct_RRLF  = applyDefault (-infinity) ct_RRLF
    , ct_IPCBA = applyDefault 0.0 ct_IPCBA
    }
  where
    infinity :: Double
    infinity = 1/0 :: Double

    applyDefault :: a -> Maybe a -> Maybe a
    applyDefault v = Just . fromMaybe v
