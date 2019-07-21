{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Language.PlutusCore.Constant.Dynamic.BuiltinName
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

import           Language.PlutusCore.Constant.Dynamic.Instances ()
import           Language.PlutusCore.Constant.Make
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Lexer.Type
import           Language.PlutusCore.Type

import           Data.Proxy
import           Debug.Trace                                    (trace)

dynamicCharToStringName :: DynamicBuiltinName
dynamicCharToStringName = DynamicBuiltinName "charToString"

dynamicCharToStringMeaning :: Evaluable uni => DynamicBuiltinNameMeaning uni
dynamicCharToStringMeaning = DynamicBuiltinNameMeaning sch pure where
    sch =
        Proxy @Char `TypeSchemeArrow`
        TypeSchemeResult (Proxy @String)

dynamicCharToStringDefinition :: Evaluable uni => DynamicBuiltinNameDefinition uni
dynamicCharToStringDefinition =
    DynamicBuiltinNameDefinition dynamicCharToStringName dynamicCharToStringMeaning

dynamicCharToString :: Term tyname name uni ()
dynamicCharToString = dynamicBuiltinNameAsTerm dynamicCharToStringName

dynamicAppendName :: DynamicBuiltinName
dynamicAppendName = DynamicBuiltinName "append"

dynamicAppendMeaning :: Evaluable uni => DynamicBuiltinNameMeaning uni
dynamicAppendMeaning = DynamicBuiltinNameMeaning sch (++) where
    sch =
        Proxy @String `TypeSchemeArrow`
        Proxy @String `TypeSchemeArrow`
        TypeSchemeResult (Proxy @String)

dynamicAppendDefinition :: Evaluable uni => DynamicBuiltinNameDefinition uni
dynamicAppendDefinition =
    DynamicBuiltinNameDefinition dynamicAppendName dynamicAppendMeaning

dynamicAppend :: Term tyname name uni ()
dynamicAppend = dynamicBuiltinNameAsTerm dynamicAppendName

dynamicTraceName :: DynamicBuiltinName
dynamicTraceName = DynamicBuiltinName "trace"

dynamicTraceMeaningMock :: Evaluable uni => DynamicBuiltinNameMeaning uni
dynamicTraceMeaningMock = DynamicBuiltinNameMeaning sch (flip trace ()) where
    sch =
        Proxy @String `TypeSchemeArrow`
        TypeSchemeResult (Proxy @())

dynamicTraceDefinitionMock :: Evaluable uni => DynamicBuiltinNameDefinition uni
dynamicTraceDefinitionMock =
    DynamicBuiltinNameDefinition dynamicTraceName dynamicTraceMeaningMock
