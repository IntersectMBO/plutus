module Marlowe.Extended.Metadata where

import Prelude
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Map (Map, keys)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Symbol (SProxy(..))
import Foreign.Generic (class Decode, class Encode, defaultOptions, genericDecode, genericEncode)
import Marlowe.Extended (Contract, ContractType(..), getChoiceNames)
import Marlowe.HasParties (getParties)
import Marlowe.Semantics as S
import Marlowe.Template (Placeholders(..), getPlaceholderIds)

data ChoiceFormat
  = DefaultFormat
  | DecimalFormat Int String

derive instance eqChoiceFormat :: Eq ChoiceFormat

derive instance genericChoiceFormat :: Generic ChoiceFormat _

instance encodeChoiceFormat :: Encode ChoiceFormat where
  encode value = genericEncode defaultOptions value

instance decodeChoiceFormat :: Decode ChoiceFormat where
  decode value = genericDecode defaultOptions value

instance showChoiceFormat :: Show ChoiceFormat where
  show = genericShow

integerFormat :: ChoiceFormat
integerFormat = DecimalFormat 0 ""

lovelaceFormat :: ChoiceFormat
lovelaceFormat = DecimalFormat 6 "₳"

oracleRatioFormat :: String -> ChoiceFormat
oracleRatioFormat str = DecimalFormat 8 str

isDefaultFormat :: ChoiceFormat -> Boolean
isDefaultFormat DefaultFormat = true

isDefaultFormat _ = false

isDecimalFormat :: ChoiceFormat -> Boolean
isDecimalFormat (DecimalFormat _ _) = true

isDecimalFormat _ = false

data ChoiceFormatType
  = DefaultFormatType
  | DecimalFormatType

derive instance eqChoiceFormatType :: Eq ChoiceFormatType

toString :: ChoiceFormatType -> String
toString DefaultFormatType = "DefaultFormatType"

toString DecimalFormatType = "DecimalFormatType"

fromString :: String -> Maybe ChoiceFormatType
fromString "DefaultFormatType" = Just DefaultFormatType

fromString "DecimalFormatType" = Just DecimalFormatType

fromString _ = Nothing

getFormatType :: ChoiceFormat -> ChoiceFormatType
getFormatType DefaultFormat = DefaultFormatType

getFormatType (DecimalFormat _ _) = DecimalFormatType

defaultForFormatType :: ChoiceFormatType -> ChoiceFormat
defaultForFormatType DefaultFormatType = DefaultFormat

defaultForFormatType DecimalFormatType = DecimalFormat 0 ""

type ChoiceInfo
  = { choiceFormat :: ChoiceFormat
    , choiceDescription :: String
    }

_choiceFormat :: Lens' ChoiceInfo ChoiceFormat
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
    , contractDescription :: String
    , roleDescriptions :: Map S.TokenName String
    , slotParameterDescriptions :: Map String String
    , valueParameterDescriptions :: Map String String
    , choiceInfo :: Map String ChoiceInfo
    }

_contractName :: Lens' MetaData String
_contractName = prop (SProxy :: SProxy "contractName")

_contractType :: Lens' MetaData ContractType
_contractType = prop (SProxy :: SProxy "contractType")

_contractDescription :: Lens' MetaData String
_contractDescription = prop (SProxy :: SProxy "contractDescription")

_roleDescriptions :: Lens' MetaData (Map S.TokenName String)
_roleDescriptions = prop (SProxy :: SProxy "roleDescriptions")

_slotParameterDescriptions :: Lens' MetaData (Map String String)
_slotParameterDescriptions = prop (SProxy :: SProxy "slotParameterDescriptions")

_valueParameterDescriptions :: Lens' MetaData (Map String String)
_valueParameterDescriptions = prop (SProxy :: SProxy "valueParameterDescriptions")

_choiceInfo :: Lens' MetaData (Map String ChoiceInfo)
_choiceInfo = prop (SProxy :: SProxy "choiceInfo")

emptyContractMetadata :: MetaData
emptyContractMetadata =
  { contractType: Other
  , contractName: ""
  , contractDescription: ""
  , roleDescriptions: mempty
  , slotParameterDescriptions: mempty
  , valueParameterDescriptions: mempty
  , choiceInfo: mempty
  }

type MetadataHintInfo
  = { roles :: Set S.TokenName
    , slotParameters :: Set String
    , valueParameters :: Set String
    , choiceNames :: Set String
    }

_roles :: Lens' MetadataHintInfo (Set S.TokenName)
_roles = prop (SProxy :: SProxy "roles")

_slotParameters :: Lens' MetadataHintInfo (Set String)
_slotParameters = prop (SProxy :: SProxy "slotParameters")

_valueParameters :: Lens' MetadataHintInfo (Set String)
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
    , slotParameters: placeholders.slotPlaceholderIds
    , valueParameters: placeholders.valuePlaceholderIds
    , choiceNames: getChoiceNames contract
    }

getHintsFromMetadata :: MetaData -> MetadataHintInfo
getHintsFromMetadata { roleDescriptions
, slotParameterDescriptions
, valueParameterDescriptions
, choiceInfo
} =
  { roles: keys roleDescriptions
  , slotParameters: keys slotParameterDescriptions
  , valueParameters: keys valueParameterDescriptions
  , choiceNames: keys choiceInfo
  }

type ContractTemplate
  = { metaData :: MetaData
    , extendedContract :: Contract
    }
