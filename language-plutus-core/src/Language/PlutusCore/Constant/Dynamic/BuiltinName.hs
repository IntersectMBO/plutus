{-# LANGUAGE DataKinds         #-}
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

import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Core
import           Language.PlutusCore.Evaluation.Machine.ExBudgeting
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Universe

import           Data.Proxy
import           Debug.Trace                                        (trace)

dynamicCharToStringName :: DynamicBuiltinName
dynamicCharToStringName = DynamicBuiltinName "charToString"

dynamicCharToStringMeaning
    :: (GShow uni, GEq uni, uni `IncludesAll` '[String, Char])
    => DynamicBuiltinNameMeaning uni -- TODO the costing function
dynamicCharToStringMeaning = DynamicBuiltinNameMeaning sch pure (\_ -> ExBudget 1 1) where
    sch =
        Proxy @Char `TypeSchemeArrow`
        TypeSchemeResult (Proxy @String)

dynamicCharToStringDefinition
    :: (GShow uni, GEq uni, uni `IncludesAll` '[String, Char])
    => DynamicBuiltinNameDefinition uni
dynamicCharToStringDefinition =
    DynamicBuiltinNameDefinition dynamicCharToStringName dynamicCharToStringMeaning

dynamicCharToString :: Term tyname name uni ()
dynamicCharToString = dynamicBuiltinNameAsTerm dynamicCharToStringName

dynamicAppendName :: DynamicBuiltinName
dynamicAppendName = DynamicBuiltinName "append"

dynamicAppendMeaning
    :: (GShow uni, GEq uni, uni `Includes` String)
    => DynamicBuiltinNameMeaning uni -- TODO the costing function
dynamicAppendMeaning = DynamicBuiltinNameMeaning sch (++) (\_ _ -> ExBudget 1 1) where
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
    :: (GShow uni, GEq uni, uni `IncludesAll` '[String, ()])
    => DynamicBuiltinNameMeaning uni -- TODO the costing function
dynamicTraceMeaningMock = DynamicBuiltinNameMeaning sch (flip trace ()) (\_ -> ExBudget 1 1) where
    sch =
        Proxy @String `TypeSchemeArrow`
        TypeSchemeResult (Proxy @())

dynamicTraceDefinitionMock
    :: (GShow uni, GEq uni, uni `IncludesAll` '[String, ()])
    => DynamicBuiltinNameDefinition uni
dynamicTraceDefinitionMock =
    DynamicBuiltinNameDefinition dynamicTraceName dynamicTraceMeaningMock
