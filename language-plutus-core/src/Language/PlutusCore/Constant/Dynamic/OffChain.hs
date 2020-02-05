{-# LANGUAGE TypeOperators #-}

module Language.PlutusCore.Constant.Dynamic.OffChain
    ( getStringBuiltinTypes
    ) where

import           Language.PlutusCore.Constant.Dynamic.BuiltinName
import           Language.PlutusCore.Constant.Function
import           Language.PlutusCore.Constant.Universe
import           Language.PlutusCore.Error
import           Language.PlutusCore.Quote
import           Language.PlutusCore.TypeCheck

import           Control.Monad.Except

getStringBuiltinTypes
    :: ( AsTypeError e uni ann, MonadError e m, MonadQuote m
       , GShow uni, GEq uni, uni `Includes` Integer, uni `Includes` String, uni `Includes` Char
       )
    => ann -> m (DynamicBuiltinNameTypes uni)
getStringBuiltinTypes ann =
       dynamicBuiltinNameMeaningsToTypes ann $
       insertDynamicBuiltinNameDefinition dynamicTraceDefinitionMock $
       insertDynamicBuiltinNameDefinition dynamicCharToStringDefinition $
       insertDynamicBuiltinNameDefinition dynamicAppendDefinition mempty
