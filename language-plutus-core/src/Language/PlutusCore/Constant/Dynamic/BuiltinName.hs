{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

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
import           Language.PlutusCore.Constant.Universe
import           Language.PlutusCore.Core

import           Data.Proxy
import           Debug.Trace                                    (trace)

dynamicCharToStringName :: DynamicBuiltinName
dynamicCharToStringName = DynamicBuiltinName "charToString"

dynamicCharToStringMeaning
    :: (GShow uni, GEq uni, uni `Includes` String, uni `Includes` Char)
    => DynamicBuiltinNameMeaning uni
dynamicCharToStringMeaning = DynamicBuiltinNameMeaning sch pure where
    sch =
        Proxy @Char `TypeSchemeArrow`
        TypeSchemeResult (Proxy @String)

dynamicCharToStringDefinition
    :: (GShow uni, GEq uni, uni `Includes` String, uni `Includes` Char)
    => DynamicBuiltinNameDefinition uni
dynamicCharToStringDefinition =
    DynamicBuiltinNameDefinition dynamicCharToStringName dynamicCharToStringMeaning

dynamicCharToString :: Term tyname name uni ()
dynamicCharToString = dynamicBuiltinNameAsTerm dynamicCharToStringName

dynamicAppendName :: DynamicBuiltinName
dynamicAppendName = DynamicBuiltinName "append"

dynamicAppendMeaning
    :: (GShow uni, GEq uni, uni `Includes` String)
    => DynamicBuiltinNameMeaning uni
dynamicAppendMeaning = DynamicBuiltinNameMeaning sch (++) where
    sch =
        Proxy @String `TypeSchemeArrow`
        Proxy @String `TypeSchemeArrow`
        TypeSchemeResult (Proxy @String)

dynamicAppendDefinition
    :: (GShow uni, GEq uni, uni `Includes` String)
    => DynamicBuiltinNameDefinition uni
dynamicAppendDefinition =
    DynamicBuiltinNameDefinition dynamicAppendName dynamicAppendMeaning

dynamicAppend :: Term tyname name uni ()
dynamicAppend = dynamicBuiltinNameAsTerm dynamicAppendName

dynamicTraceName :: DynamicBuiltinName
dynamicTraceName = DynamicBuiltinName "trace"

dynamicTraceMeaningMock
    :: (GShow uni, GEq uni, uni `Includes` Integer, uni `Includes` String)
    => DynamicBuiltinNameMeaning uni
dynamicTraceMeaningMock = DynamicBuiltinNameMeaning sch (flip trace ()) where
    sch =
        Proxy @String `TypeSchemeArrow`
        TypeSchemeResult (Proxy @())

dynamicTraceDefinitionMock
    :: (GShow uni, GEq uni, uni `Includes` Integer, uni `Includes` String)
    => DynamicBuiltinNameDefinition uni
dynamicTraceDefinitionMock =
    DynamicBuiltinNameDefinition dynamicTraceName dynamicTraceMeaningMock
