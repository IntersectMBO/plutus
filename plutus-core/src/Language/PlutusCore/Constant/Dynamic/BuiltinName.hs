{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeFamilies      #-}
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
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `IncludesAll` '[String, Char])
    => DynamicBuiltinNameMeaning term -- TODO the costing function
dynamicCharToStringMeaning = DynamicBuiltinNameMeaning sch pure (\_ -> ExBudget 1 1) where
    sch =
        Proxy @Char `TypeSchemeArrow`
        TypeSchemeResult (Proxy @String)

dynamicCharToStringDefinition
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `IncludesAll` '[String, Char])
    => DynamicBuiltinNameDefinition term
dynamicCharToStringDefinition =
    DynamicBuiltinNameDefinition dynamicCharToStringName dynamicCharToStringMeaning

dynamicCharToString :: Term tyname name uni fun ()
dynamicCharToString = dynamicBuiltinNameAsTerm dynamicCharToStringName

dynamicAppendName :: DynamicBuiltinName
dynamicAppendName = DynamicBuiltinName "append"

dynamicAppendMeaning
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `Includes` String)
    => DynamicBuiltinNameMeaning term -- TODO the costing function
dynamicAppendMeaning = DynamicBuiltinNameMeaning sch (++) (\_ _ -> ExBudget 1 1) where
    sch =
        Proxy @String `TypeSchemeArrow`
        Proxy @String `TypeSchemeArrow`
        TypeSchemeResult (Proxy @String)

dynamicAppendDefinition
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `Includes` String)
    => DynamicBuiltinNameDefinition term
dynamicAppendDefinition =
    DynamicBuiltinNameDefinition dynamicAppendName dynamicAppendMeaning

dynamicAppend :: Term tyname name uni fun ()
dynamicAppend = dynamicBuiltinNameAsTerm dynamicAppendName

dynamicTraceName :: DynamicBuiltinName
dynamicTraceName = DynamicBuiltinName "trace"

dynamicTraceMeaningMock
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `IncludesAll` '[String, ()])
    => DynamicBuiltinNameMeaning term -- TODO the costing function
dynamicTraceMeaningMock = DynamicBuiltinNameMeaning sch (flip trace ()) (\_ -> ExBudget 1 1) where
    sch =
        Proxy @String `TypeSchemeArrow`
        TypeSchemeResult (Proxy @())

dynamicTraceDefinitionMock
    :: (HasConstantIn uni term, GShow uni, GEq uni, uni `IncludesAll` '[String, ()])
    => DynamicBuiltinNameDefinition term
dynamicTraceDefinitionMock =
    DynamicBuiltinNameDefinition dynamicTraceName dynamicTraceMeaningMock
