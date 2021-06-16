module Marlowe.Extended.Metadata where

import Prelude
import Data.Lens (Lens')
import Data.Lens.Record (prop)
import Data.Map (Map, keys)
import Data.Maybe (Maybe(..))
import Data.Set (Set)
import Data.Set as Set
import Data.Symbol (SProxy(..))
import Marlowe.Extended (Contract, ContractType(..), getChoiceNames)
import Marlowe.Template (Placeholders(..), getPlaceholderIds)
import Marlowe.HasParties (getParties)
import Marlowe.Semantics as S

type MetaData
  = { contractType :: ContractType
    , contractName :: String
    , contractDescription :: String
    , roleDescriptions :: Map S.TokenName String
    , slotParameterDescriptions :: Map String String
    , valueParameterDescriptions :: Map String String
    , choiceDescriptions :: Map String String
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

_choiceDescriptions :: Lens' MetaData (Map String String)
_choiceDescriptions = prop (SProxy :: SProxy "choiceDescriptions")

emptyContractMetadata :: MetaData
emptyContractMetadata =
  { contractType: Other
  , contractName: ""
  , contractDescription: ""
  , roleDescriptions: mempty
  , slotParameterDescriptions: mempty
  , valueParameterDescriptions: mempty
  , choiceDescriptions: mempty
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
, choiceDescriptions
} =
  { roles: keys roleDescriptions
  , slotParameters: keys slotParameterDescriptions
  , valueParameters: keys valueParameterDescriptions
  , choiceNames: keys choiceDescriptions
  }

type ContractTemplate
  = { metaData :: MetaData
    , extendedContract :: Contract
    }
