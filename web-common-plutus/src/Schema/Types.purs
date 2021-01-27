module Schema.Types where

import Prelude
import Chain.Types (_value)
import Data.Array as Array
import Data.BigInteger (BigInteger)
import Data.Foldable (fold, foldMap)
import Data.Functor.Foldable (Fix(..))
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Json.JsonTuple (JsonTuple)
import Data.Lens (_2, _Just, over, set)
import Data.Lens.Index (ix)
import Data.Lens.Iso.Newtype (_Newtype)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Monoid.Additive (Additive(..))
import Data.Newtype (unwrap)
import Data.RawJson (RawJson)
import Data.String.Extra as String
import Data.Traversable (sequence, traverse)
import Data.Tuple (Tuple)
import Data.Tuple.Nested ((/\))
import Foreign (Foreign)
import Foreign.Class (encode)
import Foreign.Object as FO
import Language.PlutusTx.AssocMap as AssocMap
import Plutus.V1.Ledger.Interval (Extended(..), Interval(..), LowerBound(..), UpperBound(..))
import Plutus.V1.Ledger.Slot (Slot)
import Plutus.V1.Ledger.Value (CurrencySymbol(..), Value(..))
import Matryoshka (Algebra, ana, cata)
import Playground.Lenses (_recipient, _amount)
import Playground.Types (ContractCall(..), FunctionSchema(..), KnownCurrency(..), _PayToWallet)
import Schema (FormArgumentF(..), FormSchema(..))
import ValueEditor (ValueEvent(..))
import Wallet.Emulator.Wallet (Wallet)

data SimulationAction
  = ModifyActions ActionEvent
  | PopulateAction Int FormEvent

derive instance genericSimulationAction :: Generic SimulationAction _

instance showSimulationAction :: Show SimulationAction where
  show = genericShow

data FormEvent
  = SetField FieldEvent
  | SetSubField Int FormEvent
  | AddSubField
  | RemoveSubField Int

derive instance genericFormEvent :: Generic FormEvent _

instance showFormEvent :: Show FormEvent where
  show value = genericShow value

data FieldEvent
  = SetIntField (Maybe Int)
  | SetBigIntegerField (Maybe BigInteger)
  | SetBoolField Boolean
  | SetStringField String
  | SetHexField String
  | SetRadioField String
  | SetValueField ValueEvent
  | SetSlotRangeField (Interval Slot)

derive instance genericFieldEvent :: Generic FieldEvent _

instance showFieldEvent :: Show FieldEvent where
  show = genericShow

data ActionEvent
  = AddAction (ContractCall FormArgument)
  | AddWaitAction BigInteger
  | RemoveAction Int
  | SetWaitTime Int BigInteger
  | SetWaitUntilTime Int Slot
  | SetPayToWalletValue Int ValueEvent
  | SetPayToWalletRecipient Int Wallet

derive instance genericActionEvent :: Generic ActionEvent _

instance showActionEvent :: Show ActionEvent where
  show = genericShow

type Expression
  = ContractCall RawJson

type FormArgument
  = Fix FormArgumentF

type Signatures
  = Array (FunctionSchema FormSchema)

toArgument :: Value -> FormSchema -> FormArgument
toArgument initialValue = ana algebra
  where
  algebra :: FormSchema -> FormArgumentF FormSchema
  algebra FormSchemaUnit = FormUnitF

  algebra FormSchemaBool = FormBoolF false

  algebra FormSchemaInt = FormIntF Nothing

  algebra FormSchemaInteger = FormIntegerF Nothing

  -- text inputs cannot distinguish between `Nothing` and `Just ""` -
  -- use the latter as the default value, or validation behaves weirdly
  algebra FormSchemaString = FormStringF (Just "")

  algebra FormSchemaHex = FormHexF Nothing

  algebra (FormSchemaRadio xs) = FormRadioF xs Nothing

  algebra (FormSchemaArray xs) = FormArrayF xs []

  algebra (FormSchemaMaybe x) = FormMaybeF x Nothing

  algebra FormSchemaValue = FormValueF initialValue

  algebra FormSchemaSlotRange = FormSlotRangeF defaultSlotRange

  algebra (FormSchemaTuple a b) = FormTupleF a b

  algebra (FormSchemaObject xs) = FormObjectF xs

  algebra (FormSchemaUnsupported x) = FormUnsupportedF x

defaultSlotRange :: Interval Slot
defaultSlotRange =
  Interval
    { ivFrom: LowerBound NegInf true
    , ivTo: UpperBound PosInf true
    }

formArgumentToJson :: FormArgument -> Maybe Foreign
formArgumentToJson = cata algebra
  where
  algebra :: Algebra FormArgumentF (Maybe Foreign)
  algebra FormUnitF = Just $ encode (mempty :: Array Unit)

  algebra (FormBoolF b) = Just $ encode b

  algebra (FormIntF n) = encode <$> n

  algebra (FormIntegerF n) = encode <$> n

  algebra (FormStringF str) = encode <$> str

  algebra (FormRadioF _ option) = encode <$> option

  algebra (FormHexF str) = encode <<< String.toHex <$> str

  algebra (FormTupleF (Just fieldA) (Just fieldB)) = Just $ encode [ fieldA, fieldB ]

  algebra (FormTupleF _ _) = Nothing

  algebra (FormMaybeF _ field) = encode <$> field

  algebra (FormArrayF _ fields) = Just $ encode fields

  algebra (FormObjectF fields) = encodeFields fields
    where
    encodeFields :: Array (JsonTuple String (Maybe Foreign)) -> Maybe Foreign
    encodeFields xs = map (encode <<< FO.fromFoldable) $ prepareObject xs

    prepareObject :: Array (JsonTuple String (Maybe Foreign)) -> Maybe (Array (Tuple String Foreign))
    prepareObject = traverse processTuples

    processTuples :: JsonTuple String (Maybe Foreign) -> Maybe (Tuple String Foreign)
    processTuples = unwrap >>> sequence

  algebra (FormValueF x) = Just $ encode x

  algebra (FormSlotRangeF x) = Just $ encode x

  algebra (FormUnsupportedF _) = Nothing

mkInitialValue :: Array KnownCurrency -> BigInteger -> Value
mkInitialValue currencies initialBalance = Value { getValue: value }
  where
  value =
    map (map unwrap)
      $ fold
      $ foldMap
          ( \(KnownCurrency { hash, knownTokens }) ->
              map
                ( \tokenName ->
                    AssocMap.fromTuples
                      [ CurrencySymbol { unCurrencySymbol: hash }
                          /\ AssocMap.fromTuples [ tokenName /\ Additive initialBalance ]
                      ]
                )
                $ Array.fromFoldable knownTokens
          )
          currencies

handleFormEvent ::
  Value ->
  FormEvent ->
  FormArgument ->
  FormArgument
handleFormEvent initialValue event = cata (Fix <<< algebra event)
  where
  algebra (SetField (SetIntField n)) (FormIntF _) = FormIntF n

  algebra (SetField (SetBigIntegerField n)) (FormIntegerF _) = FormIntegerF n

  algebra (SetField (SetBoolField n)) (FormBoolF _) = FormBoolF n

  algebra (SetField (SetStringField s)) (FormStringF _) = FormStringF (Just s)

  algebra (SetField (SetHexField s)) (FormHexF _) = FormHexF (Just s)

  algebra (SetField (SetRadioField s)) (FormRadioF options _) = FormRadioF options (Just s)

  algebra (SetField (SetValueField valueEvent)) (FormValueF value) = FormValueF $ handleValueEvent valueEvent value

  algebra (SetField (SetSlotRangeField newInterval)) arg@(FormSlotRangeF _) = FormSlotRangeF newInterval

  algebra (SetSubField 1 subEvent) (FormTupleF field1 field2) = FormTupleF (handleFormEvent initialValue subEvent field1) field2

  algebra (SetSubField 2 subEvent) (FormTupleF field1 field2) = FormTupleF field1 (handleFormEvent initialValue subEvent field2)

  algebra (SetSubField 0 subEvent) (FormMaybeF schema field) = FormMaybeF schema $ over _Just (handleFormEvent initialValue subEvent) field

  algebra (SetSubField n subEvent) (FormArrayF schema fields) = FormArrayF schema $ over (ix n) (handleFormEvent initialValue subEvent) fields

  algebra (SetSubField n subEvent) s@(FormObjectF fields) = FormObjectF $ over (ix n <<< _Newtype <<< _2) (handleFormEvent initialValue subEvent) fields

  -- As the code stands, this is the only guarantee we get that every
  -- value in the array will conform to the schema: the fact that we
  -- create the 'empty' version from the same schema template.
  -- Is more type safety than that possible? Probably.
  -- Is it worth the research effort? Perhaps. :thinking_face:
  algebra AddSubField (FormArrayF schema fields) = FormArrayF schema $ Array.snoc fields (toArgument initialValue schema)

  algebra AddSubField arg = arg

  algebra (RemoveSubField n) arg@(FormArrayF schema fields) = (FormArrayF schema (fromMaybe fields (Array.deleteAt n fields)))

  algebra _ arg = arg

handleActionEvent :: ActionEvent -> Array (ContractCall FormArgument) -> Array (ContractCall FormArgument)
handleActionEvent (AddAction action) = flip Array.snoc action

handleActionEvent (AddWaitAction blocks) = flip Array.snoc (AddBlocks { blocks })

handleActionEvent (RemoveAction index) = fromMaybe <*> Array.deleteAt index

handleActionEvent (SetWaitTime index blocks) = set (ix index) (AddBlocks { blocks })

handleActionEvent (SetPayToWalletValue index valueEvent) = over (ix index <<< _PayToWallet <<< _amount) (handleValueEvent valueEvent)

handleActionEvent (SetPayToWalletRecipient index recipient) = set (ix index <<< _PayToWallet <<< _recipient) recipient

handleActionEvent (SetWaitUntilTime index slot) = set (ix index) (AddBlocksUntil { slot })

handleValueEvent :: ValueEvent -> Value -> Value
handleValueEvent (SetBalance currencySymbol tokenName amount) = set (_value <<< ix currencySymbol <<< ix tokenName) amount

-- | This only exists because of the orphan instance restriction.
traverseFunctionSchema ::
  forall m a b.
  Applicative m =>
  (a -> m b) ->
  FunctionSchema a -> m (FunctionSchema b)
traverseFunctionSchema f (FunctionSchema { endpointDescription, argument: oldArgument }) = rewrap <$> f oldArgument
  where
  rewrap newArgument = FunctionSchema { endpointDescription, argument: newArgument }
