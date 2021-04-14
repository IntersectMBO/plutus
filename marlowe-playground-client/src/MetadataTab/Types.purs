module MetadataTab.Types where

import Marlowe.Extended (ContractType)
import Marlowe.Semantics as S

class ShowConstructor a where
  showConstructor :: a -> String

data MetadataAction
  = SetContractName String
  | SetContractType ContractType
  | SetContractDescription String
  | SetRoleDescription S.TokenName String
  | DeleteRoleDescription S.TokenName
  | SetSlotParameterDescription String String
  | DeleteSlotParameterDescription String
  | SetValueParameterDescription String String
  | DeleteValueParameterDescription String
  | SetChoiceDescription String String
  | DeleteChoiceDescription String

instance metadataActionShowConstructor :: ShowConstructor MetadataAction where
  showConstructor (SetContractName _) = "SetContractName"
  showConstructor (SetContractType _) = "SetContractType"
  showConstructor (SetContractDescription _) = "SetContractDescription"
  showConstructor (SetRoleDescription _ _) = "SetRoleDescription"
  showConstructor (DeleteRoleDescription _) = "DeleteRoleDescription"
  showConstructor (SetSlotParameterDescription _ _) = "SetSlotParameterDescription"
  showConstructor (DeleteSlotParameterDescription _) = "DeleteSlotParameterDescription"
  showConstructor (SetValueParameterDescription _ _) = "SetValueParameterDescription"
  showConstructor (DeleteValueParameterDescription _) = "DeleteValueParameterDescription"
  showConstructor (SetChoiceDescription _ _) = "SetChoiceDescription"
  showConstructor (DeleteChoiceDescription _) = "DeleteChoiceDescription"
