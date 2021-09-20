module Marlowe.Parser
  ( parseContract
  , ContractParseError(..)
  ) where

import Data.BigInteger (BigInteger)
import Data.BigInteger as BigInteger
import Data.Either (Either(..))
import Data.Function.Uncurried (Fn5, runFn5)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Effect.Exception.Unsafe (unsafeThrow)
import Marlowe.Holes (AccountId, Action(..), Bound(..), Case(..), ChoiceId(..), Contract(..), Location(..), Observation(..), Party(..), Payee(..), Term(..), TermWrapper(..), Timeout(SlotParam), Token(..), Value(..), ValueId(..), getLocation, mkHole)
import Marlowe.Holes as H
import Marlowe.Semantics (Rational(..), Slot(..))
import Monaco (IRange)
import Prelude (class Show, (<<<), (>>>))

type HelperFunctions a
  = { mkHole :: String -> IRange -> Term a
    , mkTerm :: a -> IRange -> Term a
    , mkTermWrapper :: a -> IRange -> TermWrapper a
    , getRange :: Term a -> IRange
    , mkBigInteger :: Int -> BigInteger
    , mkSlot :: BigInteger -> Slot
    , mkExtendedSlot :: BigInteger -> Timeout
    , mkExtendedSlotParam :: String -> Timeout
    , mkClose :: Contract
    , mkPay :: AccountId -> Term Payee -> Term Token -> Term Value -> Term Contract -> Contract
    , mkWhen :: Array (Term Case) -> Term Timeout -> Term Contract -> Contract
    , mkIf :: Term Observation -> Term Contract -> Term Contract -> Contract
    , mkLet :: TermWrapper ValueId -> Term Value -> Term Contract -> Contract
    , mkAssert :: Term Observation -> Term Contract -> Contract
    , mkCase :: Term Action -> Term Contract -> Case
    , mkBound :: BigInteger -> BigInteger -> Bound
    , mkDeposit :: AccountId -> Term Party -> Term Token -> Term Value -> Action
    , mkChoice :: ChoiceId -> Array (Term Bound) -> Action
    , mkNotify :: Term Observation -> Action
    , mkChoiceId :: String -> Term Party -> ChoiceId
    , mkValueId :: String -> ValueId
    , mkToken :: String -> String -> Token
    , mkPK :: String -> Party
    , mkRole :: String -> Party
    , mkAccount :: AccountId -> Payee
    , mkParty :: Term Party -> Payee
    , mkAndObs :: Term Observation -> Term Observation -> Observation
    , mkOrObs :: Term Observation -> Term Observation -> Observation
    , mkNotObs :: Term Observation -> Observation
    , mkChoseSomething :: ChoiceId -> Observation
    , mkValueGE :: Term Value -> Term Value -> Observation
    , mkValueGT :: Term Value -> Term Value -> Observation
    , mkValueLT :: Term Value -> Term Value -> Observation
    , mkValueLE :: Term Value -> Term Value -> Observation
    , mkValueEQ :: Term Value -> Term Value -> Observation
    , mkTrueObs :: Observation
    , mkFalseObs :: Observation
    , mkAvailableMoney :: AccountId -> Term Token -> Value
    , mkConstant :: BigInteger -> Value
    , mkConstantParam :: String -> Value
    , mkNegValue :: Term Value -> Value
    , mkAddValue :: Term Value -> Term Value -> Value
    , mkSubValue :: Term Value -> Term Value -> Value
    , mkMulValue :: Term Value -> Term Value -> Value
    , mkRational :: BigInteger -> BigInteger -> Rational
    , mkScale :: TermWrapper Rational -> Term Value -> Value
    , mkChoiceValue :: ChoiceId -> Value
    , mkSlotIntervalStart :: Value
    , mkSlotIntervalEnd :: Value
    , mkUseValue :: TermWrapper ValueId -> Value
    , mkCond :: Term Observation -> Term Value -> Term Value -> Value
    }

-- We cannot guarantee at the type level that the only type of location we handle in the Parser is a Range
-- location, so we throw a useful error if we ever get to this situation
locationToRange :: Location -> IRange
locationToRange (Range range) = range

locationToRange (BlockId _) = unsafeThrow "Unexpected BlockId location found in MarloweParser"

locationToRange NoLocation = unsafeThrow "Unexpected NoLocation found in MarloweParser"

helperFunctions :: forall a. HelperFunctions a
helperFunctions =
  { mkHole: \h pos -> mkHole h (Range pos)
  , mkTerm: \a pos -> Term a (Range pos)
  , mkTermWrapper: \a pos -> TermWrapper a (Range pos)
  , getRange: getLocation >>> locationToRange
  , mkBigInteger: BigInteger.fromInt
  , mkSlot: Slot
  , mkExtendedSlot: H.Slot
  , mkExtendedSlotParam: SlotParam
  , mkClose: Close
  , mkPay: Pay
  , mkWhen: When
  , mkIf: If
  , mkAssert: Assert
  , mkLet: Let
  , mkCase: Case
  , mkBound: Bound
  , mkDeposit: Deposit
  , mkChoice: Choice
  , mkNotify: Notify
  , mkChoiceId: ChoiceId
  , mkValueId: ValueId
  , mkToken: Token
  , mkPK: PK
  , mkRole: Role
  , mkAccount: Account
  , mkParty: Party
  , mkAndObs: AndObs
  , mkOrObs: OrObs
  , mkNotObs: NotObs
  , mkChoseSomething: ChoseSomething
  , mkValueGE: ValueGE
  , mkValueGT: ValueGT
  , mkValueLT: ValueLT
  , mkValueLE: ValueLE
  , mkValueEQ: ValueEQ
  , mkTrueObs: TrueObs
  , mkFalseObs: FalseObs
  , mkAvailableMoney: AvailableMoney
  , mkConstant: Constant
  , mkConstantParam: ConstantParam
  , mkNegValue: NegValue
  , mkAddValue: AddValue
  , mkSubValue: SubValue
  , mkMulValue: MulValue
  , mkRational: Rational
  , mkScale: Scale
  , mkChoiceValue: ChoiceValue
  , mkSlotIntervalStart: SlotIntervalStart
  , mkSlotIntervalEnd: SlotIntervalEnd
  , mkUseValue: UseValue
  , mkCond: Cond
  }

data ContractParseError
  = EmptyInput
  | ContractParseError { message :: String, row :: Int, column :: Int, token :: String }

derive instance genericContractParseError :: Generic ContractParseError _

instance showContractParseError :: Show ContractParseError where
  show e = genericShow e

foreign import parse_ ::
  forall a.
  Fn5
    (Either ContractParseError (Term Contract))
    ({ message :: String, row :: Int, column :: Int, token :: String } -> Either ContractParseError (Term Contract))
    (Term Contract -> Either ContractParseError (Term Contract))
    (HelperFunctions a)
    String
    (Either ContractParseError (Term Contract))

parseContract :: String -> Either ContractParseError (Term Contract)
parseContract = runFn5 parse_ (Left EmptyInput) (Left <<< ContractParseError) Right helperFunctions
