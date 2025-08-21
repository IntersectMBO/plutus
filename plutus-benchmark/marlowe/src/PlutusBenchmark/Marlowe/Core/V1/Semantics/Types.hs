{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveDataTypeable    #-}
{-# LANGUAGE DerivingStrategies    #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE ViewPatterns          #-}
-- Probably could use a more specific flag but not sure what, need
-- to stop GHC inserting a clever recursive go function with no unfolding
{-# OPTIONS_GHC -O0 #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}
-- O0 turns these off
{-# OPTIONS_GHC -fno-ignore-interface-pragmas #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}

-- | Types for Marlowe semantics
module PlutusBenchmark.Marlowe.Core.V1.Semantics.Types where

import Control.Newtype.Generics (Newtype)
import Data.Data (Data)
import GHC.Generics (Generic)
import PlutusBenchmark.Marlowe.Core.V1.Semantics.Types.Address (Network)
import PlutusLedgerApi.V1.Value qualified as Val
import PlutusLedgerApi.V2 (CurrencySymbol, POSIXTime (..), TokenName)
import PlutusLedgerApi.V2 qualified as Ledger (Address (..), Credential (..), PubKeyHash (..),
                                               ScriptHash (..), StakingCredential (..))
import PlutusTx.AsData (asData)
import PlutusTx.AssocMap (Map)
import PlutusTx.AssocMap qualified as Map
import PlutusTx.IsData (FromData, ToData, UnsafeFromData, makeIsDataIndexed, unstableMakeIsData)
import PlutusTx.Lift (makeLift)
import PlutusTx.List qualified as List
import PlutusTx.Prelude (Bool (..), BuiltinByteString, Eq (..), Integer, Ord ((<=), (>=)), (&&))
import Prelude qualified as Haskell

deriving stock instance Data POSIXTime
deriving stock instance Data Ledger.Address
deriving stock instance Data Ledger.Credential
deriving stock instance Data Ledger.PubKeyHash
deriving stock instance Data Ledger.ScriptHash
deriving stock instance Data Ledger.StakingCredential

asData
  [d|
    -- \| A Party to a contract.
    data Party
      = Address Network Ledger.Address
      | -- \^ Party identified by a network address.
        Role TokenName
      -- \^ Party identified by a role token name.
      deriving stock (Generic, Data)
      deriving newtype
        ( ToData
        , FromData
        , UnsafeFromData
        , Haskell.Eq
        , Haskell.Ord
        , Haskell.Show
        , Eq
        )
    |]

-- | A party's internal account in a contract.
type AccountId = Party

-- | A timeout in a contract.
type Timeout = POSIXTime

-- | A multi-asset value.
type Money = Val.Value

-- | The name of a choice in a contract.
type ChoiceName = BuiltinByteString

-- | A numeric choice in a contract.
type ChosenNum = Integer

{-| The time validity range for a Marlowe transaction,
inclusive of both endpoints.
-}
type TimeInterval = (POSIXTime, POSIXTime)

asData
  [d|
    -- \| Choices – of integers – are identified by ChoiceId which combines
    -- a name for the choice with the Party who had made the choice.
    data ChoiceId = ChoiceId BuiltinByteString Party
      deriving stock (Generic, Data)
      deriving newtype
        ( ToData
        , FromData
        , UnsafeFromData
        , Haskell.Eq
        , Haskell.Ord
        , Haskell.Show
        , Eq
        )
    |]

asData
  [d|
    -- \| Token - represents a currency or token, it groups
    --   a pair of a currency symbol and token name.
    data Token = Token CurrencySymbol TokenName
      deriving stock (Generic, Data)
      deriving newtype
        ( ToData
        , FromData
        , UnsafeFromData
        , Haskell.Eq
        , Haskell.Ord
        , Haskell.Show
        , Eq
        )
    |]

-- | The accounts in a contract.
type Accounts = Map (AccountId, Token) Integer

{-| Values, as defined using Let ar e identified by name,
  and can be used by 'UseValue' construct.
-}
newtype ValueId = ValueId BuiltinByteString
  deriving (Haskell.Show) via TokenName
  deriving stock (Haskell.Eq, Haskell.Ord, Generic, Data)
  deriving anyclass (Newtype)
  deriving newtype (Eq)

makeIsDataIndexed ''ValueId [('ValueId, 0)]

{-| Values include some quantities that change with time,
  including “the time interval”, “the current balance of an account”,
  and any choices that have already been made.

  Values can also be scaled, and combined using addition, subtraction,
  and negation.
-}
data Value a
  = AvailableMoney AccountId Token
  | Constant Integer
  | NegValue (Value a)
  | AddValue (Value a) (Value a)
  | SubValue (Value a) (Value a)
  | MulValue (Value a) (Value a)
  | DivValue (Value a) (Value a)
  | ChoiceValue ChoiceId
  | TimeIntervalStart
  | TimeIntervalEnd
  | UseValue ValueId
  | Cond a (Value a) (Value a)
  deriving stock (Generic, Data)
  deriving stock (Haskell.Eq, Haskell.Ord, Haskell.Show)

instance (Eq a) => Eq (Value a) where
  {-# INLINEABLE (==) #-}
  AvailableMoney acc1 tok1 == AvailableMoney acc2 tok2 =
    acc1 == acc2 && tok1 == tok2
  AvailableMoney _ _ == _ = False
  Constant i1 == Constant i2 = i1 == i2
  Constant{} == _ = False
  NegValue val1 == NegValue val2 = val1 == val2
  NegValue{} == _ = False
  AddValue val1 val2 == AddValue val3 val4 = val1 == val3 && val2 == val4
  AddValue{} == _ = False
  SubValue val1 val2 == SubValue val3 val4 = val1 == val3 && val2 == val4
  SubValue{} == _ = False
  MulValue val1 val2 == MulValue val3 val4 = val1 == val3 && val2 == val4
  MulValue{} == _ = False
  DivValue val1 val2 == DivValue val3 val4 = val1 == val3 && val2 == val4
  DivValue{} == _ = False
  ChoiceValue cid1 == ChoiceValue cid2 = cid1 == cid2
  ChoiceValue{} == _ = False
  TimeIntervalStart == TimeIntervalStart = True
  TimeIntervalStart == _ = False
  TimeIntervalEnd == TimeIntervalEnd = True
  TimeIntervalEnd == _ = False
  UseValue val1 == UseValue val2 = val1 == val2
  UseValue{} == _ = False
  Cond obs1 thn1 els1 == Cond obs2 thn2 els2 =
    obs1 == obs2 && thn1 == thn2 && els1 == els2
  Cond{} == _ = False

unstableMakeIsData ''Value

{-| Observations are Boolean values derived by comparing values,
  and can be combined using the standard Boolean operators.

  It is also possible to observe whether any choice has been made
  (for a particular identified choice).
-}
data Observation
  = AndObs Observation Observation
  | OrObs Observation Observation
  | NotObs Observation
  | ChoseSomething ChoiceId
  | ValueGE (Value Observation) (Value Observation)
  | ValueGT (Value Observation) (Value Observation)
  | ValueLT (Value Observation) (Value Observation)
  | ValueLE (Value Observation) (Value Observation)
  | ValueEQ (Value Observation) (Value Observation)
  | TrueObs
  | FalseObs
  deriving stock (Generic, Data)
  deriving stock (Haskell.Eq, Haskell.Ord, Haskell.Show)

instance Eq Observation where
  {-# INLINEABLE (==) #-}
  AndObs o1l o2l == AndObs o1r o2r           = o1l == o1r && o2l == o2r
  AndObs{} == _                              = False
  OrObs o1l o2l == OrObs o1r o2r             = o1l == o1r && o2l == o2r
  OrObs{} == _                               = False
  NotObs ol == NotObs or                     = ol == or
  NotObs{} == _                              = False
  ChoseSomething cid1 == ChoseSomething cid2 = cid1 == cid2
  ChoseSomething _ == _                      = False
  ValueGE v1l v2l == ValueGE v1r v2r         = v1l == v1r && v2l == v2r
  ValueGE{} == _                             = False
  ValueGT v1l v2l == ValueGT v1r v2r         = v1l == v1r && v2l == v2r
  ValueGT{} == _                             = False
  ValueLT v1l v2l == ValueLT v1r v2r         = v1l == v1r && v2l == v2r
  ValueLT{} == _                             = False
  ValueLE v1l v2l == ValueLE v1r v2r         = v1l == v1r && v2l == v2r
  ValueLE{} == _                             = False
  ValueEQ v1l v2l == ValueEQ v1r v2r         = v1l == v1r && v2l == v2r
  ValueEQ{} == _                             = False
  TrueObs == TrueObs                         = True
  TrueObs == _                               = False
  FalseObs == FalseObs                       = True
  FalseObs == _                              = False

unstableMakeIsData ''Observation

asData
  [d|
    -- \| The (inclusive) bound on a choice number.
    data Bound = Bound Integer Integer
      deriving stock (Generic, Data)
      deriving newtype
        ( ToData
        , FromData
        , UnsafeFromData
        , Haskell.Eq
        , Haskell.Ord
        , Haskell.Show
        , Eq
        )
    |]

asData
  [d|
    -- \| Actions happen at particular points during execution.
    --   Three kinds of action are possible:
    --
    --   * A @Deposit n p v@ makes a deposit of value @v@ into account @n@
    --     belonging to party @p@.
    --
    --   * A choice is made for a particular id with a list of bounds on the
    --     values that are acceptable.
    --     For example, @[(0, 0), (3, 5]@ offers the choice of one of 0, 3, 4
    --     and 5.
    --
    --   * The contract is notified that a particular observation be made.
    --     Typically this would be done by one of the parties,
    --     or one of their wallets acting automatically.
    data Action
      = Deposit AccountId Party Token (Value Observation)
      | Choice ChoiceId [Bound]
      | Notify Observation
      deriving stock (Generic, Data)
      deriving newtype
        ( ToData
        , FromData
        , UnsafeFromData
        , Haskell.Eq
        , Haskell.Ord
        , Haskell.Show
        , Eq
        )
    |]

asData
  [d|
    -- \| A payment can be made to one of the parties to the contract,
    --   or to one of the accounts of the contract,
    --   and this is reflected in the definition.
    data Payee
      = Account AccountId
      | Party Party
      deriving stock (Generic, Data)
      deriving newtype
        ( ToData
        , FromData
        , UnsafeFromData
        , Haskell.Eq
        , Haskell.Ord
        , Haskell.Show
        , Eq
        )
    |]

asData
  [d|
    -- \| A case is a branch of a when clause, guarded by an action.
    --   The continuation of the contract may be merkleized or not.
    --
    --   Plutus doesn't support mutually recursive data types yet.
    --   datatype Case is mutually recursive with @Contract@
    data Case a
      = Case Action a
      | MerkleizedCase Action BuiltinByteString
      deriving stock (Generic, Data)
      deriving newtype
        ( ToData
        , FromData
        , UnsafeFromData
        , Haskell.Eq
        , Haskell.Ord
        , Haskell.Show
        , Eq
        )
    |]

-- | Extract the @Action@ from a @Case@.
getAction :: (ToData a, UnsafeFromData a) => Case a -> Action
getAction (Case action _)           = action
getAction (MerkleizedCase action _) = action
{-# INLINEABLE getAction #-}

asData
  [d|
    -- \| Marlowe has six ways of building contracts.
    --   Five of these – 'Pay', 'Let', 'If', 'When' and 'Assert' –
    --   build a complex contract from simpler contracts, and the sixth,
    --   'Close', is a simple contract.
    --   At each step of execution, as well as returning a new state and
    --   continuation contract, it is possible that effects – payments –
    --   and warnings can be generated too.
    data Contract
      = Close
      | Pay AccountId Payee Token (Value Observation) Contract
      | If Observation Contract Contract
      | When [Case Contract] Timeout Contract
      | Let ValueId (Value Observation) Contract
      | Assert Observation Contract
      deriving stock (Generic, Data)
      -- deriving stock (Haskell.Eq, Haskell.Ord, Haskell.Show)
      deriving newtype
        ( ToData
        , FromData
        , UnsafeFromData
        , Haskell.Eq
        , Haskell.Ord
        , Haskell.Show
        , Eq
        )
    |]

asData
  [d|
    -- \| Marlowe contract internal state. Stored in a /Datum/ of a
    -- transaction output.
    data State = State
      { accounts :: Accounts
      , choices :: Map ChoiceId ChosenNum
      , boundValues :: Map ValueId Integer
      , minTime :: POSIXTime
      }
      deriving stock (Generic, Data)
      deriving newtype
        ( ToData
        , FromData
        , UnsafeFromData
        , Haskell.Eq
        , Haskell.Ord
        , Haskell.Show
        , Eq
        )
    |]

{-# INLINEABLE State #-}

-- | Execution environment. Contains a time interval of a transaction.
newtype Environment = Environment {timeInterval :: TimeInterval}
  deriving stock (Haskell.Show, Haskell.Eq, Haskell.Ord, Data)
  deriving newtype (Eq)

makeIsDataIndexed ''Environment [('Environment, 0)]

asData
  [d|
    -- \| Input for a Marlowe contract. Correspond to expected 'Action's.
    data InputContent
      = IDeposit AccountId Party Token Integer
      | IChoice ChoiceId ChosenNum
      | INotify
      deriving stock (Generic, Data)
      deriving newtype
        ( ToData
        , FromData
        , UnsafeFromData
        , Haskell.Eq
        , Haskell.Ord
        , Haskell.Show
        , Eq
        )
    |]

asData
  [d|
    -- \| Input to a contract, which may include the merkleized continuation
    --   of the contract and its hash.
    data Input
      = NormalInput InputContent
      | MerkleizedInput InputContent BuiltinByteString Contract
      deriving stock (Generic, Data)
      deriving newtype
        ( ToData
        , FromData
        , UnsafeFromData
        , Haskell.Eq
        , Haskell.Ord
        , Haskell.Show
        , Eq
        )
    |]

-- | Extract the content of input.
getInputContent :: Input -> InputContent
getInputContent (NormalInput inputContent)         = inputContent
getInputContent (MerkleizedInput inputContent _ _) = inputContent
{-# INLINEABLE getInputContent #-}

{-| Time interval errors.
  'InvalidInterval' means @slotStart > slotEnd@, and
  'IntervalInPastError' means time interval is in the past,
  relative to the contract.

  These errors should never occur, but we are always prepared.
-}
data IntervalError
  = InvalidInterval TimeInterval
  | IntervalInPastError POSIXTime TimeInterval
  deriving stock (Haskell.Show, Haskell.Eq, Generic, Data)

-- | Result of 'fixInterval'
data IntervalResult
  = IntervalTrimmed Environment State
  | IntervalError IntervalError
  deriving stock (Haskell.Show, Generic, Data)

-- | Empty State for a given minimal 'POSIXTime'
emptyState :: POSIXTime -> State
emptyState sn =
  State
    { accounts = Map.empty
    , choices = Map.empty
    , boundValues = Map.empty
    , minTime = sn
    }
{-# INLINEABLE emptyState #-}

-- | Check if a 'num' is withint a list of inclusive bounds.
inBounds :: ChosenNum -> [Bound] -> Bool
inBounds num = List.any (\(Bound l u) -> num >= l && num <= u)
{-# INLINEABLE inBounds #-}

makeLift ''Party
makeLift ''ChoiceId
makeLift ''Token
makeLift ''ValueId
makeLift ''Value
makeLift ''Observation
makeLift ''Bound
makeLift ''Action
makeLift ''Case
makeLift ''Payee
makeLift ''Contract
makeLift ''State
makeLift ''Environment
makeLift ''InputContent
makeLift ''Input
