{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE TypeOperators #-}

module Language.PlutusCore.Constant.Dynamic.OffChain
    ( getStringBuiltinMeanings
    , getStringBuiltinTypes
    ) where

import           Language.PlutusCore.Constant.Dynamic.BuiltinName
import           Language.PlutusCore.Constant.Function
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Error
import           Language.PlutusCore.Quote
import           Language.PlutusCore.TypeCheck
import           Language.PlutusCore.Universe

import           Control.Monad.Except

getStringBuiltinMeanings
    :: (GShow uni, GEq uni, uni `IncludesAll` [String, Char, ()])
    => DynamicBuiltinNameMeanings uni
getStringBuiltinMeanings =
       insertDynamicBuiltinNameDefinition dynamicTraceDefinitionMock $
       insertDynamicBuiltinNameDefinition dynamicCharToStringDefinition $
       insertDynamicBuiltinNameDefinition dynamicAppendDefinition mempty

getStringBuiltinTypes
    :: ( AsTypeError e uni ann, MonadError e m, MonadQuote m
       , GShow uni, GEq uni, uni `IncludesAll` '[String, Char, ()]
       )
    => ann -> m (DynamicBuiltinNameTypes uni)
getStringBuiltinTypes ann =
       dynamicBuiltinNameMeaningsToTypes ann getStringBuiltinMeanings
