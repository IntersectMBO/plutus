module Schema.Types where

import Data.Lens
import Prelude
import Chain.Types (_value)
import Data.Array as Array
import Data.Foldable (fold, foldMap)
import Data.Functor.Foldable (Fix(..))
import Data.Json.JsonTuple (JsonTuple)
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
import Ledger.Interval (Extended(..), Interval(..), LowerBound(..), UpperBound(..))
import Ledger.Slot (Slot)
import Ledger.Value (CurrencySymbol(..), Value(..))
import Matryoshka (Algebra, ana, cata)
import Playground.Types (ContractCall(..), KnownCurrency(..), _PayToWallet)
import Schema (FormArgumentF(..), FormSchema(..))
import Playground.Lenses (_recipient, _amount)
import ValueEditor (ValueEvent(..))
import Wallet.Emulator.Wallet (Wallet)

data SimulationAction
  = ModifyActions ActionEvent
  | PopulateAction Int Int FormEvent

data FormEvent
  = SetField FieldEvent
  | SetSubField Int FormEvent
  | AddSubField
  | RemoveSubField Int

data FieldEvent
  = SetIntField (Maybe Int)
  | SetBoolField Boolean
  | SetStringField String
  | SetHexField String
  | SetRadioField String
  | SetValueField ValueEvent
  | SetSlotRangeField (Interval Slot)

data ActionEvent
  = AddAction SimulatorAction
  | AddWaitAction Int
  | RemoveAction Int
  | SetWaitTime Int Int
  | SetWaitUntilTime Int Slot
  | SetPayToWalletValue Int ValueEvent
  | SetPayToWalletRecipient Int Wallet

type SimulatorAction
  = ContractCall FormArgument

type Expression
  = ContractCall RawJson

type FormArgument
  = Fix FormArgumentF

toArgument :: Value -> FormSchema -> FormArgument
toArgument initialValue = ana algebra
  where
  algebra :: FormSchema -> FormArgumentF FormSchema
  algebra FormSchemaUnit = FormUnitF

  algebra FormSchemaBool = FormBoolF false

  algebra FormSchemaInt = FormIntF Nothing

  algebra FormSchemaString = FormStringF Nothing

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

mkInitialValue :: Array KnownCurrency -> Int -> Value
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

handleActionForm ::
  Value ->
  FormEvent ->
  FormArgument ->
  FormArgument
handleActionForm initialValue event = cata (Fix <<< algebra event)
  where
  algebra (SetField (SetIntField n)) (FormIntF _) = FormIntF n

  algebra (SetField (SetBoolField n)) (FormBoolF _) = FormBoolF n

  algebra (SetField (SetStringField s)) (FormStringF _) = FormStringF (Just s)

  algebra (SetField (SetHexField s)) (FormHexF _) = FormHexF (Just s)

  algebra (SetField (SetRadioField s)) (FormRadioF options _) = FormRadioF options (Just s)

  algebra (SetField (SetValueField valueEvent)) (FormValueF value) = FormValueF $ handleActionValueEvent valueEvent value

  algebra (SetField (SetSlotRangeField newInterval)) arg@(FormSlotRangeF _) = FormSlotRangeF newInterval

  algebra (SetSubField 1 subEvent) (FormTupleF field1 field2) = FormTupleF (handleActionForm initialValue subEvent field1) field2

  algebra (SetSubField 1 subEvent) (FormTupleF field1 field2) = FormTupleF field1 (handleActionForm initialValue subEvent field2)

  algebra (SetSubField 0 subEvent) (FormMaybeF schema field) = FormMaybeF schema $ over _Just (handleActionForm initialValue subEvent) field

  algebra (SetSubField n subEvent) (FormArrayF schema fields) = FormArrayF schema $ over (ix n) (handleActionForm initialValue subEvent) fields

  algebra (SetSubField n subEvent) s@(FormObjectF fields) = FormObjectF $ over (ix n <<< _Newtype <<< _2) (handleActionForm initialValue subEvent) fields

  -- As the code stands, this is the only guarantee we get that every
  -- value in the array will conform to the schema: the fact that we
  -- create the 'empty' version from the same schema template.
  -- Is more type safety than that possible? Probably.
  -- Is it worth the research effort? Perhaps. :thinking_face:
  algebra AddSubField (FormArrayF schema fields) = FormArrayF schema $ Array.snoc fields (toArgument initialValue schema)

  algebra AddSubField arg = arg

  algebra (RemoveSubField n) arg@(FormArrayF schema fields) = (FormArrayF schema (fromMaybe fields (Array.deleteAt n fields)))

  algebra _ arg = arg

handleActionValueEvent :: ValueEvent -> Value -> Value
handleActionValueEvent (SetBalance currencySymbol tokenName amount) = set (_value <<< ix currencySymbol <<< ix tokenName) amount

handleActionActionEvent :: ActionEvent -> Array SimulatorAction -> Array SimulatorAction
handleActionActionEvent (AddAction action) = flip Array.snoc action

handleActionActionEvent (AddWaitAction blocks) = flip Array.snoc (AddBlocks { blocks })

handleActionActionEvent (RemoveAction index) = fromMaybe <*> Array.deleteAt index

handleActionActionEvent (SetWaitTime index blocks) = set (ix index) (AddBlocks { blocks })

handleActionActionEvent (SetPayToWalletValue index valueEvent) = over (ix index <<< _PayToWallet <<< _amount) (handleActionValueEvent valueEvent)

handleActionActionEvent (SetPayToWalletRecipient index recipient) = set (ix index <<< _PayToWallet <<< _recipient) recipient

handleActionActionEvent (SetWaitUntilTime index slot) = set (ix index) (AddBlocksUntil { slot })
