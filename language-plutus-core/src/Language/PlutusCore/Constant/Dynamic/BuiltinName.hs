{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Language.PlutusCore.Constant.Dynamic.BuiltinName
    ( dynamicIntToStringName
    , dynamicIntToStringMeaning
    , dynamicIntToStringDefinition
    , dynamicIntToString
    , dynamicAppendName
    , dynamicAppendMeaning
    , dynamicAppendDefinition
    , dynamicAppend
    ) where

import           Language.PlutusCore.Constant.Dynamic.Instances ()
import           Language.PlutusCore.Constant.Make
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Lexer.Type
import           Language.PlutusCore.Type

dynamicIntToStringName :: DynamicBuiltinName
dynamicIntToStringName = DynamicBuiltinName "intToString"

dynamicIntToStringMeaning :: DynamicBuiltinNameMeaning
dynamicIntToStringMeaning = DynamicBuiltinNameMeaning sch show where
    sch =
        TypeSchemeAllSize $ \s ->
            TypeSchemeBuiltin (TypedBuiltinSized (SizeBound s) TypedBuiltinSizedInt) `TypeSchemeArrow`
            TypeSchemeBuiltin (TypedBuiltinDyn @String)

dynamicIntToStringDefinition :: DynamicBuiltinNameDefinition
dynamicIntToStringDefinition =
    DynamicBuiltinNameDefinition dynamicIntToStringName dynamicIntToStringMeaning

dynamicIntToString :: Term tyname name ()
dynamicIntToString = dynamicBuiltinNameAsTerm dynamicIntToStringName

dynamicAppendName :: DynamicBuiltinName
dynamicAppendName = DynamicBuiltinName "append"

dynamicAppendMeaning :: DynamicBuiltinNameMeaning
dynamicAppendMeaning = DynamicBuiltinNameMeaning sch (++) where
    sch =
        TypeSchemeBuiltin (TypedBuiltinDyn @String) `TypeSchemeArrow`
        TypeSchemeBuiltin (TypedBuiltinDyn @String) `TypeSchemeArrow`
        TypeSchemeBuiltin (TypedBuiltinDyn @String)

dynamicAppendDefinition :: DynamicBuiltinNameDefinition
dynamicAppendDefinition =
    DynamicBuiltinNameDefinition dynamicAppendName dynamicAppendMeaning

dynamicAppend :: Term tyname name ()
dynamicAppend = dynamicBuiltinNameAsTerm dynamicAppendName
