module Marlowe.Extended.Metadata where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Symbol (SProxy(..))
import Foreign.Generic (class Decode, class Encode, defaultOptions, genericDecode, genericEncode)
import Marlowe.Extended (Contract, ContractType(..), getChoiceNames)
import Data.Map.Ordered.OMap (OMap)
import Data.Map.Ordered.OMap as OMap
import Data.Set.Ordered.OSet (OSet)
import Data.Set.Ordered.OSet as OSet
import Marlowe.HasParties (getParties)
import Marlowe.Semantics as S
import Marlowe.Template (Placeholders(..), getPlaceholderIds)

data NumberFormat
  = DefaultFormat
  | DecimalFormat Int String
  | TimeFormat

derive instance eqNumberFormat :: Eq NumberFormat

derive instance genericNumberFormat :: Generic NumberFormat _

instance encodeNumberFormat :: Encode NumberFormat where
  encode value = genericEncode defaultOptions value

instance decodeNumberFormat :: Decode NumberFormat where
  decode value = genericDecode defaultOptions value

instance showNumberFormat :: Show NumberFormat where
  show = genericShow

integerFormat :: NumberFormat
integerFormat = DecimalFormat 0 ""

lovelaceFormat :: NumberFormat
lovelaceFormat = DecimalFormat 6 "₳"

oracleRatioFormat :: String -> NumberFormat
oracleRatioFormat str = DecimalFormat 8 str

isDefaultFormat :: NumberFormat -> Boolean
isDefaultFormat DefaultFormat = true

isDefaultFormat _ = false

isDecimalFormat :: NumberFormat -> Boolean
isDecimalFormat (DecimalFormat _ _) = true

isDecimalFormat _ = false

data NumberFormatType
  = DefaultFormatType
  | DecimalFormatType
  | TimeFormatType

derive instance eqNumberFormatType :: Eq NumberFormatType

toString :: NumberFormatType -> String
toString DefaultFormatType = "DefaultFormatType"

toString DecimalFormatType = "DecimalFormatType"

toString TimeFormatType = "TimeFormatType"

fromString :: String -> Maybe NumberFormatType
fromString "DefaultFormatType" = Just DefaultFormatType

fromString "DecimalFormatType" = Just DecimalFormatType

fromString _ = Nothing

getFormatType :: NumberFormat -> NumberFormatType
getFormatType DefaultFormat = DefaultFormatType

getFormatType (DecimalFormat _ _) = DecimalFormatType

getFormatType TimeFormat = TimeFormatType

defaultForFormatType :: NumberFormatType -> NumberFormat
defaultForFormatType DefaultFormatType = DefaultFormat

defaultForFormatType DecimalFormatType = DecimalFormat 0 ""

defaultForFormatType TimeFormatType = TimeFormat

type ValueParameterInfo
  = { valueParameterFormat :: NumberFormat
    , valueParameterDescription :: String
    }

_valueParameterFormat :: Lens' ValueParameterInfo NumberFormat
_valueParameterFormat = prop (SProxy :: SProxy "valueParameterFormat")

_valueParameterDescription :: Lens' ValueParameterInfo String
_valueParameterDescription = prop (SProxy :: SProxy "valueParameterDescription")

emptyValueParameterInfo :: ValueParameterInfo
emptyValueParameterInfo =
  { valueParameterFormat: DefaultFormat
  , valueParameterDescription: mempty
  }

getValueParameterInfo :: String -> OMap String ValueParameterInfo -> ValueParameterInfo
getValueParameterInfo str = fromMaybe emptyValueParameterInfo <<< OMap.lookup str

updateValueParameterInfo :: (ValueParameterInfo -> ValueParameterInfo) -> String -> OMap String ValueParameterInfo -> OMap String ValueParameterInfo
updateValueParameterInfo f = OMap.alter updateValueParameterInfoEntry
  where
  updateValueParameterInfoEntry :: Maybe ValueParameterInfo -> Maybe ValueParameterInfo
  updateValueParameterInfoEntry mValueParameterInfo = Just $ f $ fromMaybe emptyValueParameterInfo mValueParameterInfo

type ChoiceInfo
  = { choiceFormat :: NumberFormat
    , choiceDescription :: String
    }

_choiceFormat :: Lens' ChoiceInfo NumberFormat
_choiceFormat = prop (SProxy :: SProxy "choiceFormat")

_choiceDescription :: Lens' ChoiceInfo String
_choiceDescription = prop (SProxy :: SProxy "choiceDescription")

emptyChoiceInfo :: ChoiceInfo
emptyChoiceInfo =
  { choiceFormat: DefaultFormat
  , choiceDescription: mempty
  }

getChoiceInfo :: String -> Map String ChoiceInfo -> ChoiceInfo
getChoiceInfo str = fromMaybe emptyChoiceInfo <<< Map.lookup str

updateChoiceInfo :: (ChoiceInfo -> ChoiceInfo) -> String -> Map String ChoiceInfo -> Map String ChoiceInfo
updateChoiceInfo f = Map.alter updateChoiceInfoEntry
  where
  updateChoiceInfoEntry :: Maybe ChoiceInfo -> Maybe ChoiceInfo
  updateChoiceInfoEntry mChoiceInfo = Just $ f $ fromMaybe emptyChoiceInfo mChoiceInfo

type MetaData
  = { contractType :: ContractType
    , contractName :: String
    , contractShortDescription :: String
    , contractLongDescription :: String
    , roleDescriptions :: Map S.TokenName String
    , slotParameterDescriptions :: OMap String String
    , valueParameterInfo :: OMap String ValueParameterInfo
    , choiceInfo :: Map String ChoiceInfo
    }

_contractName :: Lens' MetaData String
_contractName = prop (SProxy :: SProxy "contractName")

_contractType :: Lens' MetaData ContractType
_contractType = prop (SProxy :: SProxy "contractType")

_contractShortDescription :: Lens' MetaData String
_contractShortDescription = prop (SProxy :: SProxy "contractShortDescription")

_contractLongDescription :: Lens' MetaData String
_contractLongDescription = prop (SProxy :: SProxy "contractLongDescription")

_roleDescriptions :: Lens' MetaData (Map S.TokenName String)
_roleDescriptions = prop (SProxy :: SProxy "roleDescriptions")

_slotParameterDescriptions :: Lens' MetaData (OMap String String)
_slotParameterDescriptions = prop (SProxy :: SProxy "slotParameterDescriptions")

_valueParameterInfo :: Lens' MetaData (OMap String ValueParameterInfo)
_valueParameterInfo = prop (SProxy :: SProxy "valueParameterInfo")

_choiceInfo :: Lens' MetaData (Map String ChoiceInfo)
_choiceInfo = prop (SProxy :: SProxy "choiceInfo")

emptyContractMetadata :: MetaData
emptyContractMetadata =
  { contractType: Other
  , contractName: ""
  , contractShortDescription: ""
  , contractLongDescription: ""
  , roleDescriptions: mempty
  , slotParameterDescriptions: mempty
  , valueParameterInfo: mempty
  , choiceInfo: mempty
  }

getChoiceFormat :: MetaData -> String -> NumberFormat
getChoiceFormat { choiceInfo } choiceName = maybe DefaultFormat (\choiceInfoVal -> choiceInfoVal.choiceFormat) $ Map.lookup choiceName choiceInfo

type MetadataHintInfo
  = { roles :: Set S.TokenName
    , slotParameters :: OSet String
    , valueParameters :: OSet String
    , choiceNames :: Set String
    }

_roles :: Lens' MetadataHintInfo (Set S.TokenName)
_roles = prop (SProxy :: SProxy "roles")

_slotParameters :: Lens' MetadataHintInfo (OSet String)
_slotParameters = prop (SProxy :: SProxy "slotParameters")

_valueParameters :: Lens' MetadataHintInfo (OSet String)
_valueParameters = prop (SProxy :: SProxy "valueParameters")

_choiceNames :: Lens' MetadataHintInfo (Set String)
_choiceNames = prop (SProxy :: SProxy "choiceNames")

getMetadataHintInfo :: Contract -> MetadataHintInfo
getMetadataHintInfo contract =
  let
    Placeholders placeholders = getPlaceholderIds contract
  in
    { roles:
        Set.mapMaybe
          ( case _ of
              S.Role name -> Just name
              _ -> Nothing
          )
          $ getParties contract
    , slotParameters: OSet.fromFoldable (placeholders.slotPlaceholderIds)
    , valueParameters: OSet.fromFoldable (placeholders.valuePlaceholderIds)
    , choiceNames: getChoiceNames contract
    }

getHintsFromMetadata :: MetaData -> MetadataHintInfo
getHintsFromMetadata { roleDescriptions
, slotParameterDescriptions
, valueParameterInfo
, choiceInfo
} =
  { roles: Map.keys roleDescriptions
  , slotParameters: OMap.keys slotParameterDescriptions
  , valueParameters: OMap.keys valueParameterInfo
  , choiceNames: Map.keys choiceInfo
  }

type ContractTemplate
  = { metaData :: MetaData
    , extendedContract :: Contract
    }

_metaData :: Lens' ContractTemplate MetaData
_metaData = prop (SProxy :: SProxy "metaData")

_extendedContract :: Lens' ContractTemplate Contract
_extendedContract = prop (SProxy :: SProxy "extendedContract")
