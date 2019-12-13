{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Language.PlutusCore.Merkle.Constant.Dynamic.BuiltinName
    ( dynamicCharToStringName
    , dynamicCharToStringMeaning
    , dynamicCharToStringDefinition
    , dynamicCharToString
    , dynamicAppendName
    , dynamicAppendMeaning
    , dynamicAppendDefinition
    , dynamicAppend
    , dynamicTraceName
    , dynamicTraceMeaningMock
    , dynamicTraceDefinitionMock
    ) where

import           Language.PlutusCore.Lexer.Type
import           Language.PlutusCore.Merkle.Constant.Dynamic.Instances ()
import           Language.PlutusCore.Merkle.Constant.Make
import           Language.PlutusCore.Merkle.Constant.Typed
import           Language.PlutusCore.Type

import           Data.Proxy
import           Debug.Trace                                           (trace)

dynamicCharToStringName :: DynamicBuiltinName
dynamicCharToStringName = DynamicBuiltinName "charToString"

dynamicCharToStringMeaning :: DynamicBuiltinNameMeaning
dynamicCharToStringMeaning = DynamicBuiltinNameMeaning sch pure where
    sch =
        Proxy @Char `TypeSchemeArrow`
        TypeSchemeResult (Proxy @String)

dynamicCharToStringDefinition :: DynamicBuiltinNameDefinition
dynamicCharToStringDefinition =
    DynamicBuiltinNameDefinition dynamicCharToStringName dynamicCharToStringMeaning

dynamicCharToString :: Term tyname name Integer
dynamicCharToString = dynamicBuiltinNameAsTerm dynamicCharToStringName

dynamicAppendName :: DynamicBuiltinName
dynamicAppendName = DynamicBuiltinName "append"

dynamicAppendMeaning :: DynamicBuiltinNameMeaning
dynamicAppendMeaning = DynamicBuiltinNameMeaning sch (++) where
    sch =
        Proxy @String `TypeSchemeArrow`
        Proxy @String `TypeSchemeArrow`
        TypeSchemeResult (Proxy @String)

dynamicAppendDefinition :: DynamicBuiltinNameDefinition
dynamicAppendDefinition =
    DynamicBuiltinNameDefinition dynamicAppendName dynamicAppendMeaning

dynamicAppend :: Term tyname name Integer
dynamicAppend = dynamicBuiltinNameAsTerm dynamicAppendName

dynamicTraceName :: DynamicBuiltinName
dynamicTraceName = DynamicBuiltinName "trace"

dynamicTraceMeaningMock :: DynamicBuiltinNameMeaning
dynamicTraceMeaningMock = DynamicBuiltinNameMeaning sch (flip trace ()) where
    sch =
        Proxy @String `TypeSchemeArrow`
        TypeSchemeResult (Proxy @())

dynamicTraceDefinitionMock :: DynamicBuiltinNameDefinition
dynamicTraceDefinitionMock =
    DynamicBuiltinNameDefinition dynamicTraceName dynamicTraceMeaningMock
