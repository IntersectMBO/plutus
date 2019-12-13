module Language.PlutusCore.Merkle.Constant.Dynamic.OffChain ( getStringBuiltinTypes ) where

import           Control.Monad.Except
import           Language.PlutusCore.Error
import           Language.PlutusCore.Merkle.Constant.Dynamic.BuiltinName
import           Language.PlutusCore.Merkle.Constant.Function
import           Language.PlutusCore.Quote
import           Language.PlutusCore.TypeCheck

getStringBuiltinTypes
    :: (AsTypeError e ann, MonadError e m, MonadQuote m) => ann -> m DynamicBuiltinNameTypes
getStringBuiltinTypes ann = error "OffChain: getStringBuiltinTypes"
    --   dynamicBuiltinNameMeaningsToTypes ann
    -- $
    --   insertDynamicBuiltinNameDefinition dynamicTraceDefinitionMock $
    --   insertDynamicBuiltinNameDefinition dynamicCharToStringDefinition $
    --   insertDynamicBuiltinNameDefinition dynamicAppendDefinition mempty

