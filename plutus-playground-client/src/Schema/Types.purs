module Schema.Types where

import Data.RawJson (JsonTuple(..))
import Data.Tuple (Tuple(..))
import Schema (Constructor(..), ConstructorName(..), DataType(..), TypeSignature(..))

textDataType :: DataType
textDataType =
  DataType
    ( TypeSignature
        { argumentSignatures: []
        , constructorName: "Text"
        , moduleName: "Data.Text.Internal"
        }
    )
    []

stringDataType :: DataType
stringDataType =
  DataType
    ( TypeSignature
        { argumentSignatures: []
        , constructorName: "String"
        , moduleName: "GHC.Types"
        }
    )
    []

intSignature :: TypeSignature
intSignature =
  TypeSignature
    { argumentSignatures: []
    , constructorName: "Int"
    , moduleName: "GHC.Types"
    }

intDataType :: DataType
intDataType = DataType intSignature []

integerDataType :: DataType
integerDataType = DataType integerSignature []

integerSignature :: TypeSignature
integerSignature =
  TypeSignature
    { argumentSignatures: []
    , constructorName: "Integer"
    , moduleName: "GHC.Integer.Type"
    }

tokenNameSignature :: TypeSignature
tokenNameSignature =
  TypeSignature
    { argumentSignatures: []
    , constructorName: "TokenName"
    , moduleName: "Ledger.Value"
    }

currencySymbolSignature :: TypeSignature
currencySymbolSignature =
  TypeSignature
    { argumentSignatures: []
    , constructorName: "CurrencySymbol"
    , moduleName: "Ledger.Value"
    }

tupleSignature :: TypeSignature -> TypeSignature -> TypeSignature
tupleSignature a b =
  TypeSignature
    { moduleName: "GHC.Tuple"
    , constructorName: "(,)"
    , argumentSignatures: [ a, b ]
    }

assocMapSignature :: TypeSignature -> TypeSignature -> TypeSignature
assocMapSignature k v =
  TypeSignature
    { moduleName: "Language.PlutusTx.AssocMap"
    , constructorName: "Map"
    , argumentSignatures: [ k, v ]
    }

listSignature :: TypeSignature -> TypeSignature
listSignature a =
  TypeSignature
    { moduleName: "GHC.Types"
    , constructorName: "[]"
    , argumentSignatures: [ a ]
    }

maybeDataType :: DataType -> DataType
maybeDataType a@(DataType aSignature _) =
  DataType
    ( TypeSignature
        { moduleName: "GHC.Maybe"
        , constructorName: "Maybe"
        , argumentSignatures: [ aSignature ]
        }
    )
    [ Constructor (ConstructorName "Nothing") []
    , Constructor (ConstructorName "Just") [ a ]
    ]

valueDataType :: DataType
valueDataType =
  DataType
    ( listSignature
        ( tupleSignature
            currencySymbolSignature
            ( assocMapSignature
                tokenNameSignature
                integerSignature
            )
        )
    )
    []
