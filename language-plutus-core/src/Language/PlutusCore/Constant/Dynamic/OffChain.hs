{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}

module Language.PlutusCore.Constant.Dynamic.OffChain
    ( getStringBuiltinMeanings
    ) where

import           Language.PlutusCore.Constant.Dynamic.BuiltinName
import           Language.PlutusCore.Constant.Function
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Universe

getStringBuiltinMeanings
    :: (GShow uni, GEq uni, uni `IncludesAll` [String, Char, ()])
    => DynamicBuiltinNameMeanings uni
getStringBuiltinMeanings =
       insertDynamicBuiltinNameDefinition dynamicTraceDefinitionMock $
       insertDynamicBuiltinNameDefinition dynamicCharToStringDefinition $
       insertDynamicBuiltinNameDefinition dynamicAppendDefinition mempty
