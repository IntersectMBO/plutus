module Marlowe.Extended where

import Prelude
import Control.Alt ((<|>))
import Data.BigInteger (BigInteger)
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Lens (Lens')
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Lens.Record (prop)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Newtype (class Newtype, unwrap)
import Data.Set (Set)
import Data.Set as Set
import Data.Symbol (SProxy(..))
import Data.Traversable (foldMap, traverse)
import Foreign (ForeignError(..), fail)
import Foreign.Class (class Encode, class Decode, encode, decode)
import Foreign.Index (hasProperty)
import Marlowe.Semantics (decodeProp)
import Marlowe.Semantics as S
import Text.Pretty (class Args, class Pretty, genericHasArgs, genericHasNestedArgs, genericPretty, pretty)

data ContractType
  = Escrow
  | EscrowWithCollateral
  | ZeroCouponBond
  | CouponBondGuaranteed
  | Swap
  | ContractForDifferences
  | Other

derive instance genericContractType :: Generic ContractType _

derive instance eqContractType :: Eq ContractType

instance showContractType :: Show ContractType where
  show v = genericShow v

contractTypeArray :: Array ContractType
contractTypeArray = [ Escrow, EscrowWithCollateral, ZeroCouponBond, CouponBondGuaranteed, Swap, ContractForDifferences, Other ]

contractTypeInitials :: ContractType -> String
contractTypeInitials Escrow = "ES"

contractTypeInitials EscrowWithCollateral = "EC"

contractTypeInitials ZeroCouponBond = "ZC"

contractTypeInitials CouponBondGuaranteed = "CB"

contractTypeInitials Swap = "S"

contractTypeInitials ContractForDifferences = "CD"

contractTypeInitials Other = "O"

contractTypeName :: ContractType -> String
contractTypeName Escrow = "Escrow"

contractTypeName EscrowWithCollateral = "Escrow with Collateral"

contractTypeName ZeroCouponBond = "Zero Coupon Bond"

contractTypeName CouponBondGuaranteed = "Coupon Bond Guaranteed"

contractTypeName Swap = "Swap"

contractTypeName ContractForDifferences = "Contract for Differences"

contractTypeName Other = "Other"

initialsToContractType :: String -> ContractType
initialsToContractType "ES" = Escrow

initialsToContractType "EC" = EscrowWithCollateral

initialsToContractType "ZC" = ZeroCouponBond

initialsToContractType "CB" = CouponBondGuaranteed

initialsToContractType "S" = Swap

initialsToContractType "CD" = ContractForDifferences

initialsToContractType _ = Other

instance encodeJsonContractType :: Encode ContractType where
  encode = encode <<< contractTypeInitials

instance decodeJsonContractType :: Decode ContractType where
  decode ct = decode ct >>= pure <<< initialsToContractType

class ToCore a b where
  toCore :: a -> Maybe b

-- TODO: Move to Marlowe.Extended.Template
newtype Placeholders
  = Placeholders
  { slotPlaceholderIds :: Set String
  , valuePlaceholderIds :: Set String
  }

derive instance newTypePlaceholders :: Newtype Placeholders _

derive newtype instance semigroupPlaceholders :: Semigroup Placeholders

derive newtype instance monoidPlaceholders :: Monoid Placeholders

-- TODO: Move to Marlowe.Extended.Template
data IntegerTemplateType
  = SlotContent
  | ValueContent

newtype TemplateContent
  = TemplateContent
  { slotContent :: Map String BigInteger
  , valueContent :: Map String BigInteger
  }

_slotContent :: Lens' TemplateContent (Map String BigInteger)
_slotContent = _Newtype <<< prop (SProxy :: SProxy "slotContent")

_valueContent :: Lens' TemplateContent (Map String BigInteger)
_valueContent = _Newtype <<< prop (SProxy :: SProxy "valueContent")

typeToLens :: IntegerTemplateType -> Lens' TemplateContent (Map String BigInteger)
typeToLens SlotContent = _slotContent

typeToLens ValueContent = _valueContent

derive instance newTypeTemplateContent :: Newtype TemplateContent _

derive newtype instance semigroupTemplateContent :: Semigroup TemplateContent

derive newtype instance monoidTemplateContent :: Monoid TemplateContent

initializeWith :: forall a b. Ord a => (a -> b) -> Set a -> Map a b
initializeWith f = foldMap (\x -> Map.singleton x $ f x)

initializeTemplateContent :: Placeholders -> TemplateContent
initializeTemplateContent ( Placeholders
    { slotPlaceholderIds, valuePlaceholderIds }
) =
  TemplateContent
    { slotContent: initializeWith (const one) slotPlaceholderIds
    , valueContent: initializeWith (const zero) valuePlaceholderIds
    }

updateTemplateContent :: Placeholders -> TemplateContent -> TemplateContent
updateTemplateContent ( Placeholders { slotPlaceholderIds, valuePlaceholderIds }
) (TemplateContent { slotContent, valueContent }) =
  TemplateContent
    { slotContent: initializeWith (\x -> fromMaybe one $ Map.lookup x slotContent) slotPlaceholderIds
    , valueContent: initializeWith (\x -> fromMaybe zero $ Map.lookup x valueContent) valuePlaceholderIds
    }

-- TODO: Move to Marlowe.Extended.Template
class Template a b where
  getPlaceholderIds :: a -> b

class Fillable a b where
  fillTemplate :: b -> a -> a

class HasChoices a where
  getChoiceNames :: a -> Set String

instance arrayHasChoices :: HasChoices a => HasChoices (Array a) where
  getChoiceNames = foldMap getChoiceNames

instance sChoiceIdHasChoices :: HasChoices S.ChoiceId where
  getChoiceNames (S.ChoiceId choiceName _) = Set.singleton choiceName

data Timeout
  = SlotParam String
  | Slot BigInteger

derive instance genericTimeout :: Generic Timeout _

derive instance eqTimeout :: Eq Timeout

derive instance ordTimeout :: Ord Timeout

instance encodeJsonTimeout :: Encode Timeout where
  encode (SlotParam str) = encode { slot_param: str }
  encode (Slot val) = encode val

instance decodeJsonTimeout :: Decode Timeout where
  decode a =
    ( SlotParam <$> decodeProp "slot_param" a
        <|> (Slot <$> decode a)
    )

instance showTimeout :: Show Timeout where
  show (Slot x) = show x
  show v = genericShow v

instance prettyTimeout :: Pretty Timeout where
  pretty (Slot x) = pretty x
  pretty v = genericPretty v

instance hasArgsTimeout :: Args Timeout where
  hasArgs (Slot _) = false
  hasArgs x = genericHasArgs x
  hasNestedArgs (Slot _) = false
  hasNestedArgs x = genericHasNestedArgs x

instance toCoreTimeout :: ToCore Timeout S.Slot where
  toCore (SlotParam _) = Nothing
  toCore (Slot x) = Just (S.Slot x)

instance templateTimeout :: Template Timeout Placeholders where
  getPlaceholderIds (SlotParam slotParamId) = Placeholders (unwrap (mempty :: Placeholders)) { slotPlaceholderIds = Set.singleton slotParamId }
  getPlaceholderIds (Slot x) = mempty

instance fillableTimeout :: Fillable Timeout TemplateContent where
  fillTemplate placeholders v@(SlotParam slotParamId) = maybe v Slot $ Map.lookup slotParamId (unwrap placeholders).slotContent
  fillTemplate _ (Slot x) = Slot x

data Value
  = AvailableMoney S.AccountId S.Token
  | Constant BigInteger
  | ConstantParam String
  | NegValue Value
  | AddValue Value Value
  | SubValue Value Value
  | MulValue Value Value
  | Scale S.Rational Value
  | ChoiceValue S.ChoiceId
  | SlotIntervalStart
  | SlotIntervalEnd
  | UseValue S.ValueId
  | Cond Observation Value Value

derive instance genericValue :: Generic Value _

derive instance eqValue :: Eq Value

derive instance ordValue :: Ord Value

instance encodeJsonValue :: Encode Value where
  encode (AvailableMoney accId tok) =
    encode
      { amount_of_token: tok
      , in_account: accId
      }
  encode (Constant val) = encode val
  encode (ConstantParam str) = encode { constant_param: str }
  encode (NegValue val) =
    encode
      { negate: val
      }
  encode (AddValue lhs rhs) =
    encode
      { add: lhs
      , and: rhs
      }
  encode (SubValue lhs rhs) =
    encode
      { value: lhs
      , minus: rhs
      }
  encode (MulValue lhs rhs) =
    encode
      { multiply: lhs
      , times: rhs
      }
  encode (Scale (S.Rational num den) val) =
    encode
      { multiply: val
      , times: num
      , divide_by: den
      }
  encode (ChoiceValue choiceId) =
    encode
      { value_of_choice: choiceId
      }
  encode SlotIntervalStart = encode "slot_interval_start"
  encode SlotIntervalEnd = encode "slot_interval_end"
  encode (UseValue valueId) =
    encode
      { use_value: valueId
      }
  encode (Cond cond thenValue elseValue) =
    encode
      { if: cond
      , then: thenValue
      , else: elseValue
      }

instance decodeJsonValue :: Decode Value where
  decode a =
    ( ifM ((\x -> x == "slot_interval_start") <$> decode a)
        (pure SlotIntervalStart)
        (fail (ForeignError "Not \"slot_interval_start\" string"))
    )
      <|> ( ifM ((\x -> x == "slot_interval_end") <$> decode a)
            (pure SlotIntervalEnd)
            (fail (ForeignError "Not \"slot_interval_end\" string"))
        )
      <|> ( AvailableMoney <$> decodeProp "in_account" a
            <*> decodeProp "amount_of_token" a
        )
      <|> (Constant <$> decode a)
      <|> ( ConstantParam <$> decodeProp "constant_param" a
        )
      <|> (NegValue <$> decodeProp "negate" a)
      <|> ( AddValue <$> decodeProp "add" a
            <*> decodeProp "and" a
        )
      <|> ( SubValue <$> decodeProp "value" a
            <*> decodeProp "minus" a
        )
      <|> ( if (hasProperty "divide_by" a) then
            ( Scale
                <$> ( S.Rational <$> decodeProp "times" a
                      <*> decodeProp "divide_by" a
                  )
                <*> decodeProp "multiply" a
            )
          else
            ( MulValue <$> decodeProp "multiply" a
                <*> decodeProp "times" a
            )
        )
      <|> (ChoiceValue <$> decodeProp "value_of_choice" a)
      <|> (UseValue <$> decodeProp "use_value" a)
      <|> ( Cond <$> decodeProp "if" a
            <*> decodeProp "then" a
            <*> decodeProp "else" a
        )

instance showValue :: Show Value where
  show v = genericShow v

instance prettyValue :: Pretty Value where
  pretty v = genericPretty v

instance hasArgsValue :: Args Value where
  hasArgs a = genericHasArgs a
  hasNestedArgs a = genericHasNestedArgs a

instance toCoreValue :: ToCore Value S.Value where
  toCore (Constant c) = Just $ S.Constant c
  toCore (ConstantParam _) = Nothing
  toCore (AvailableMoney accId tok) = S.AvailableMoney <$> pure accId <*> pure tok
  toCore (NegValue v) = S.NegValue <$> toCore v
  toCore (AddValue lhs rhs) = S.AddValue <$> toCore lhs <*> toCore rhs
  toCore (SubValue lhs rhs) = S.SubValue <$> toCore lhs <*> toCore rhs
  toCore (MulValue lhs rhs) = S.MulValue <$> toCore lhs <*> toCore rhs
  toCore (Scale f v) = S.Scale <$> pure f <*> toCore v
  toCore (ChoiceValue choId) = Just $ S.ChoiceValue choId
  toCore SlotIntervalStart = Just $ S.SlotIntervalStart
  toCore SlotIntervalEnd = Just $ S.SlotIntervalEnd
  toCore (UseValue vId) = Just $ S.UseValue vId
  toCore (Cond obs lhs rhs) = S.Cond <$> toCore obs <*> toCore lhs <*> toCore rhs

instance templateValue :: Template Value Placeholders where
  getPlaceholderIds (ConstantParam constantParamId) = Placeholders (unwrap (mempty :: Placeholders)) { valuePlaceholderIds = Set.singleton constantParamId }
  getPlaceholderIds (Constant _) = mempty
  getPlaceholderIds (AvailableMoney _ _) = mempty
  getPlaceholderIds (NegValue v) = getPlaceholderIds v
  getPlaceholderIds (AddValue lhs rhs) = getPlaceholderIds lhs <> getPlaceholderIds rhs
  getPlaceholderIds (SubValue lhs rhs) = getPlaceholderIds lhs <> getPlaceholderIds rhs
  getPlaceholderIds (MulValue lhs rhs) = getPlaceholderIds lhs <> getPlaceholderIds rhs
  getPlaceholderIds (Scale _ v) = getPlaceholderIds v
  getPlaceholderIds (ChoiceValue _) = mempty
  getPlaceholderIds SlotIntervalStart = mempty
  getPlaceholderIds SlotIntervalEnd = mempty
  getPlaceholderIds (UseValue _) = mempty
  getPlaceholderIds (Cond obs lhs rhs) = getPlaceholderIds obs <> getPlaceholderIds lhs <> getPlaceholderIds rhs

instance fillableValue :: Fillable Value TemplateContent where
  fillTemplate placeholders val = case val of
    Constant _ -> val
    ConstantParam constantParamId -> maybe val Constant $ Map.lookup constantParamId (unwrap placeholders).valueContent
    AvailableMoney _ _ -> val
    NegValue v -> NegValue $ go v
    AddValue lhs rhs -> AddValue (go lhs) (go rhs)
    SubValue lhs rhs -> SubValue (go lhs) (go rhs)
    MulValue lhs rhs -> MulValue (go lhs) (go rhs)
    Scale f v -> Scale f $ go v
    ChoiceValue _ -> val
    SlotIntervalStart -> val
    SlotIntervalEnd -> val
    UseValue _ -> val
    Cond obs lhs rhs -> Cond (go obs) (go lhs) (go rhs)
    where
    go :: forall a. (Fillable a TemplateContent) => a -> a
    go = fillTemplate placeholders

instance valueHasChoices :: HasChoices Value where
  getChoiceNames (AvailableMoney accId _) = Set.empty
  getChoiceNames (Constant _) = Set.empty
  getChoiceNames (ConstantParam _) = Set.empty
  getChoiceNames (NegValue val) = getChoiceNames val
  getChoiceNames (AddValue lhs rhs) = getChoiceNames lhs <> getChoiceNames rhs
  getChoiceNames (SubValue lhs rhs) = getChoiceNames lhs <> getChoiceNames rhs
  getChoiceNames (MulValue lhs rhs) = getChoiceNames lhs <> getChoiceNames rhs
  getChoiceNames (Scale _ val) = getChoiceNames val
  getChoiceNames (ChoiceValue choId) = getChoiceNames choId
  getChoiceNames SlotIntervalStart = Set.empty
  getChoiceNames SlotIntervalEnd = Set.empty
  getChoiceNames (UseValue _) = Set.empty
  getChoiceNames (Cond obs lhs rhs) = getChoiceNames obs <> getChoiceNames lhs <> getChoiceNames rhs

data Observation
  = AndObs Observation Observation
  | OrObs Observation Observation
  | NotObs Observation
  | ChoseSomething S.ChoiceId
  | ValueGE Value Value
  | ValueGT Value Value
  | ValueLT Value Value
  | ValueLE Value Value
  | ValueEQ Value Value
  | TrueObs
  | FalseObs

derive instance genericObservation :: Generic Observation _

derive instance eqObservation :: Eq Observation

derive instance ordObservation :: Ord Observation

instance encodeJsonObservation :: Encode Observation where
  encode (AndObs lhs rhs) =
    encode
      { both: lhs
      , and: rhs
      }
  encode (OrObs lhs rhs) =
    encode
      { either: lhs
      , or: rhs
      }
  encode (NotObs obs) =
    encode
      { not: obs
      }
  encode (ChoseSomething choiceId) =
    encode
      { chose_something_for: choiceId
      }
  encode (ValueGE lhs rhs) =
    encode
      { value: lhs
      , ge_than: rhs
      }
  encode (ValueGT lhs rhs) =
    encode
      { value: lhs
      , gt: rhs
      }
  encode (ValueLT lhs rhs) =
    encode
      { value: lhs
      , lt: rhs
      }
  encode (ValueLE lhs rhs) =
    encode
      { value: lhs
      , le_than: rhs
      }
  encode (ValueEQ lhs rhs) =
    encode
      { value: lhs
      , equal_to: rhs
      }
  encode TrueObs = encode true
  encode FalseObs = encode false

instance decodeJsonObservation :: Decode Observation where
  decode a =
    ( ifM (decode a)
        (pure TrueObs)
        (fail (ForeignError "Not a boolean"))
    )
      <|> ( ifM (not <$> decode a)
            (pure FalseObs)
            (fail (ForeignError "Not a boolean"))
        )
      <|> ( AndObs <$> decodeProp "both" a
            <*> decodeProp "and" a
        )
      <|> ( OrObs <$> decodeProp "either" a
            <*> decodeProp "or" a
        )
      <|> (NotObs <$> decodeProp "not" a)
      <|> (ChoseSomething <$> decodeProp "chose_something_for" a)
      <|> ( ValueGE <$> decodeProp "value" a
            <*> decodeProp "ge_than" a
        )
      <|> ( ValueGT <$> decodeProp "value" a
            <*> decodeProp "gt" a
        )
      <|> ( ValueLT <$> decodeProp "value" a
            <*> decodeProp "lt" a
        )
      <|> ( ValueLE <$> decodeProp "value" a
            <*> decodeProp "le_than" a
        )
      <|> ( ValueEQ <$> decodeProp "value" a
            <*> decodeProp "equal_to" a
        )

instance showObservation :: Show Observation where
  show o = genericShow o

instance prettyObservation :: Pretty Observation where
  pretty v = genericPretty v

instance hasArgsObservation :: Args Observation where
  hasArgs a = genericHasArgs a
  hasNestedArgs a = genericHasNestedArgs a

instance toCoreObservation :: ToCore Observation S.Observation where
  toCore (AndObs lhs rhs) = S.AndObs <$> toCore lhs <*> toCore rhs
  toCore (OrObs lhs rhs) = S.OrObs <$> toCore lhs <*> toCore rhs
  toCore (NotObs v) = S.NotObs <$> toCore v
  toCore (ChoseSomething choId) = Just $ S.ChoseSomething choId
  toCore (ValueGE lhs rhs) = S.ValueGE <$> toCore lhs <*> toCore rhs
  toCore (ValueGT lhs rhs) = S.ValueGT <$> toCore lhs <*> toCore rhs
  toCore (ValueLT lhs rhs) = S.ValueLT <$> toCore lhs <*> toCore rhs
  toCore (ValueLE lhs rhs) = S.ValueLE <$> toCore lhs <*> toCore rhs
  toCore (ValueEQ lhs rhs) = S.ValueEQ <$> toCore lhs <*> toCore rhs
  toCore TrueObs = Just S.TrueObs
  toCore FalseObs = Just S.FalseObs

instance templateObservation :: Template Observation Placeholders where
  getPlaceholderIds (AndObs lhs rhs) = getPlaceholderIds lhs <> getPlaceholderIds rhs
  getPlaceholderIds (OrObs lhs rhs) = getPlaceholderIds lhs <> getPlaceholderIds rhs
  getPlaceholderIds (NotObs v) = getPlaceholderIds v
  getPlaceholderIds (ChoseSomething _) = mempty
  getPlaceholderIds (ValueGE lhs rhs) = getPlaceholderIds lhs <> getPlaceholderIds rhs
  getPlaceholderIds (ValueGT lhs rhs) = getPlaceholderIds lhs <> getPlaceholderIds rhs
  getPlaceholderIds (ValueLT lhs rhs) = getPlaceholderIds lhs <> getPlaceholderIds rhs
  getPlaceholderIds (ValueLE lhs rhs) = getPlaceholderIds lhs <> getPlaceholderIds rhs
  getPlaceholderIds (ValueEQ lhs rhs) = getPlaceholderIds lhs <> getPlaceholderIds rhs
  getPlaceholderIds TrueObs = mempty
  getPlaceholderIds FalseObs = mempty

instance fillableObservation :: Fillable Observation TemplateContent where
  fillTemplate placeholders obs = case obs of
    AndObs lhs rhs -> AndObs (go lhs) (go rhs)
    OrObs lhs rhs -> OrObs (go lhs) (go rhs)
    NotObs v -> NotObs (go v)
    ChoseSomething _ -> obs
    ValueGE lhs rhs -> ValueGE (go lhs) (go rhs)
    ValueGT lhs rhs -> ValueGT (go lhs) (go rhs)
    ValueLT lhs rhs -> ValueLT (go lhs) (go rhs)
    ValueLE lhs rhs -> ValueLE (go lhs) (go rhs)
    ValueEQ lhs rhs -> ValueEQ (go lhs) (go rhs)
    TrueObs -> obs
    FalseObs -> obs
    where
    go :: forall a. (Fillable a TemplateContent) => a -> a
    go = fillTemplate placeholders

instance observationHasChoices :: HasChoices Observation where
  getChoiceNames (AndObs lhs rhs) = getChoiceNames lhs <> getChoiceNames rhs
  getChoiceNames (OrObs lhs rhs) = getChoiceNames lhs <> getChoiceNames rhs
  getChoiceNames (NotObs v) = getChoiceNames v
  getChoiceNames (ChoseSomething a) = getChoiceNames a
  getChoiceNames (ValueGE lhs rhs) = getChoiceNames lhs <> getChoiceNames rhs
  getChoiceNames (ValueGT lhs rhs) = getChoiceNames lhs <> getChoiceNames rhs
  getChoiceNames (ValueLT lhs rhs) = getChoiceNames lhs <> getChoiceNames rhs
  getChoiceNames (ValueLE lhs rhs) = getChoiceNames lhs <> getChoiceNames rhs
  getChoiceNames (ValueEQ lhs rhs) = getChoiceNames lhs <> getChoiceNames rhs
  getChoiceNames TrueObs = Set.empty
  getChoiceNames FalseObs = Set.empty

data Action
  = Deposit S.AccountId S.Party S.Token Value
  | Choice S.ChoiceId (Array S.Bound)
  | Notify Observation

derive instance genericAction :: Generic Action _

derive instance eqAction :: Eq Action

derive instance ordAction :: Ord Action

instance encodeJsonAction :: Encode Action where
  encode (Deposit accountId party token value) =
    encode
      { party: party
      , deposits: value
      , of_token: token
      , into_account: accountId
      }
  encode (Choice choiceId boundArray) =
    encode
      { choose_between: boundArray
      , for_choice: choiceId
      }
  encode (Notify obs) =
    encode
      { notify_if: obs
      }

instance decodeJsonAction :: Decode Action where
  decode a =
    ( Deposit <$> decodeProp "into_account" a
        <*> decodeProp "party" a
        <*> decodeProp "of_token" a
        <*> decodeProp "deposits" a
    )
      <|> ( Choice <$> decodeProp "for_choice" a
            <*> decodeProp "choose_between" a
        )
      <|> (Notify <$> decodeProp "notify_if" a)

instance showAction :: Show Action where
  show (Choice cid bounds) = "(Choice " <> show cid <> " " <> show bounds <> ")"
  show v = genericShow v

instance prettyAction :: Pretty Action where
  pretty v = genericPretty v

instance hasArgsAction :: Args Action where
  hasArgs a = genericHasArgs a
  hasNestedArgs a = genericHasNestedArgs a

instance toCoreAction :: ToCore Action S.Action where
  toCore (Deposit accId party tok val) = S.Deposit <$> pure accId <*> pure party <*> pure tok <*> toCore val
  toCore (Choice choId bounds) = Just $ S.Choice choId bounds
  toCore (Notify obs) = S.Notify <$> toCore obs

instance templateAction :: Template Action Placeholders where
  getPlaceholderIds (Deposit accId party tok val) = getPlaceholderIds val
  getPlaceholderIds (Choice choId bounds) = mempty
  getPlaceholderIds (Notify obs) = getPlaceholderIds obs

instance fillableAction :: Fillable Action TemplateContent where
  fillTemplate placeholders action = case action of
    Deposit accId party tok val -> Deposit accId party tok $ go val
    Choice _ _ -> action
    Notify obs -> Notify $ go obs
    where
    go :: forall a. (Fillable a TemplateContent) => a -> a
    go = fillTemplate placeholders

instance actionHasChoices :: HasChoices Action where
  getChoiceNames (Deposit _ _ _ value) = getChoiceNames value
  getChoiceNames (Choice choId _) = getChoiceNames choId
  getChoiceNames (Notify obs) = getChoiceNames obs

data Payee
  = Account S.AccountId
  | Party S.Party

derive instance genericPayee :: Generic Payee _

derive instance eqPayee :: Eq Payee

derive instance ordPayee :: Ord Payee

instance encodeJsonPayee :: Encode Payee where
  encode (Account accountId) = encode { account: accountId }
  encode (Party party) = encode { party: party }

instance decodeJsonPayee :: Decode Payee where
  decode a =
    (Account <$> decodeProp "account" a)
      <|> (Party <$> decodeProp "party" a)

instance showPayee :: Show Payee where
  show v = genericShow v

instance prettyPayee :: Pretty Payee where
  pretty v = genericPretty v

instance hasArgsPayee :: Args Payee where
  hasArgs a = genericHasArgs a
  hasNestedArgs a = genericHasNestedArgs a

instance toCorePayee :: ToCore Payee S.Payee where
  toCore (Account accId) = Just $ S.Account accId
  toCore (Party roleName) = Just $ S.Party roleName

data Case
  = Case Action Contract

derive instance genericCase :: Generic Case _

derive instance eqCase :: Eq Case

derive instance ordCase :: Ord Case

instance encodeJsonCase :: Encode Case where
  encode (Case action cont) =
    encode
      { case: action
      , then: cont
      }

instance decodeJsonCase :: Decode Case where
  decode a =
    ( Case <$> decodeProp "case" a
        <*> decodeProp "then" a
    )

instance showCase :: Show Case where
  show (Case action contract) = "Case " <> show action <> " " <> show contract

instance prettyCase :: Pretty Case where
  pretty v = genericPretty v

instance hasArgsCase :: Args Case where
  hasArgs a = genericHasArgs a
  hasNestedArgs a = genericHasNestedArgs a

instance toCoreCase :: ToCore Case S.Case where
  toCore (Case act c) = S.Case <$> toCore act <*> toCore c

instance templateCase :: Template Case Placeholders where
  getPlaceholderIds (Case act c) = getPlaceholderIds act <> getPlaceholderIds c

instance fillableCase :: Fillable Case TemplateContent where
  fillTemplate placeholders (Case act c) = Case (go act) (go c)
    where
    go :: forall a. (Fillable a TemplateContent) => a -> a
    go = fillTemplate placeholders

instance caseHasChoices :: HasChoices Case where
  getChoiceNames (Case action contract) = getChoiceNames action <> getChoiceNames contract

data Contract
  = Close
  | Pay S.AccountId Payee S.Token Value Contract
  | If Observation Contract Contract
  | When (Array Case) Timeout Contract
  | Let S.ValueId Value Contract
  | Assert Observation Contract

derive instance genericContract :: Generic Contract _

derive instance eqContract :: Eq Contract

derive instance ordContract :: Ord Contract

instance encodeJsonContract :: Encode Contract where
  encode Close = encode "close"
  encode (Pay accId payee token val cont) =
    encode
      { pay: val
      , token: token
      , from_account: accId
      , to: payee
      , then: cont
      }
  encode (If obs contTrue contFalse) =
    encode
      { if: obs
      , then: contTrue
      , else: contFalse
      }
  encode (When cases timeout cont) =
    encode
      { when: cases
      , timeout: timeout
      , timeout_continuation: cont
      }
  encode (Let valId val cont) =
    encode
      { let: valId
      , be: val
      , then: cont
      }
  encode (Assert obs cont) =
    encode
      { assert: obs
      , then: cont
      }

instance decodeJsonContract :: Decode Contract where
  decode a =
    ( ifM ((\x -> x == "close") <$> decode a)
        (pure Close)
        (fail (ForeignError "Not \"close\" string"))
    )
      <|> ( Pay <$> decodeProp "from_account" a
            <*> decodeProp "to" a
            <*> decodeProp "token" a
            <*> decodeProp "pay" a
            <*> decodeProp "then" a
        )
      <|> ( If <$> decodeProp "if" a
            <*> decodeProp "then" a
            <*> decodeProp "else" a
        )
      <|> ( When <$> decodeProp "when" a
            <*> decodeProp "timeout" a
            <*> decodeProp "timeout_continuation" a
        )
      <|> ( Let <$> decodeProp "let" a
            <*> decodeProp "be" a
            <*> decodeProp "then" a
        )
      <|> ( Assert <$> decodeProp "assert" a
            <*> decodeProp "then" a
        )

instance showContract :: Show Contract where
  show v = genericShow v

instance prettyContract :: Pretty Contract where
  pretty v = genericPretty v

instance hasArgsContract :: Args Contract where
  hasArgs a = genericHasArgs a
  hasNestedArgs a = genericHasNestedArgs a

instance toCoreContract :: ToCore Contract S.Contract where
  toCore Close = Just S.Close
  toCore (Pay accId payee tok val cont) = S.Pay <$> pure accId <*> toCore payee <*> pure tok <*> toCore val <*> toCore cont
  toCore (If obs cont1 cont2) = S.If <$> toCore obs <*> toCore cont1 <*> toCore cont2
  toCore (When cases tim cont) = S.When <$> traverse toCore cases <*> toCore tim <*> toCore cont
  toCore (Let varId val cont) = S.Let <$> pure varId <*> toCore val <*> toCore cont
  toCore (Assert obs cont) = S.Assert <$> toCore obs <*> toCore cont

instance templateContract :: Template Contract Placeholders where
  getPlaceholderIds Close = mempty
  getPlaceholderIds (Pay accId payee tok val cont) = getPlaceholderIds val <> getPlaceholderIds cont
  getPlaceholderIds (If obs cont1 cont2) = getPlaceholderIds obs <> getPlaceholderIds cont1 <> getPlaceholderIds cont2
  getPlaceholderIds (When cases tim cont) = foldMap getPlaceholderIds cases <> getPlaceholderIds tim <> getPlaceholderIds cont
  getPlaceholderIds (Let varId val cont) = getPlaceholderIds val <> getPlaceholderIds cont
  getPlaceholderIds (Assert obs cont) = getPlaceholderIds obs <> getPlaceholderIds cont

instance fillableContract :: Fillable Contract TemplateContent where
  fillTemplate placeholders contract = case contract of
    Close -> Close
    Pay accId payee tok val cont -> Pay accId payee tok (go val) (go cont)
    If obs cont1 cont2 -> If (go obs) (go cont1) (go cont2)
    When cases tim cont -> When (map go cases) (go tim) (go cont)
    Let varId val cont -> Let varId (go val) (go cont)
    Assert obs cont -> Assert (go obs) (go cont)
    where
    go :: forall a. (Fillable a TemplateContent) => a -> a
    go = fillTemplate placeholders

instance contractHasChoices :: HasChoices Contract where
  getChoiceNames Close = Set.empty
  getChoiceNames (Pay accId payee _ val cont) = getChoiceNames val <> getChoiceNames cont
  getChoiceNames (If obs cont1 cont2) = getChoiceNames obs <> getChoiceNames cont1 <> getChoiceNames cont2
  getChoiceNames (When cases _ cont) = getChoiceNames cases <> getChoiceNames cont
  getChoiceNames (Let _ val cont) = getChoiceNames val <> getChoiceNames cont
  getChoiceNames (Assert obs cont) = getChoiceNames obs <> getChoiceNames cont

-- In the extended marlowe we are treating Slot's as relative times to an initial slot and the
-- SlotParam as absolute times. This function will recurse on a contract making the relative slots
-- absolute
resolveRelativeTimes :: S.Slot -> Contract -> Contract
resolveRelativeTimes (S.Slot baseSlot) contract = relativeContract contract
  where
  relativeContract = case _ of
    Close -> Close
    Pay a p t v contract' -> Pay a p t v (relativeContract contract')
    If obs contract1 contract2 -> If obs (relativeContract contract1) (relativeContract contract2)
    When cases timeout contract' -> When (relativeCase <$> cases) (relativeTimeout timeout) (relativeContract contract')
    Let vid v contract' -> Let vid v (relativeContract contract')
    Assert obs contract' -> Assert obs (relativeContract contract')

  relativeTimeout = case _ of
    Slot t -> Slot $ t + baseSlot
    slotParam -> slotParam

  relativeCase (Case action contract') = Case action (relativeContract contract')
