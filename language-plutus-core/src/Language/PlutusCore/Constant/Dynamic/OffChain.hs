module Language.PlutusCore.Constant.Dynamic.OffChain
    ( getStringBuiltinTypes
    ) where

import           Language.PlutusCore.Constant.Dynamic.BuiltinName
import           Language.PlutusCore.Constant.Function
import           Language.PlutusCore.Error
import           Language.PlutusCore.Quote
import           Language.PlutusCore.TypeCheck

import           Control.Monad.Except

getStringBuiltinTypes
    :: (AsTypeError e ann, MonadError e m, MonadQuote m) => ann -> m DynamicBuiltinNameTypes
getStringBuiltinTypes ann =
       dynamicBuiltinNameMeaningsToTypes ann $
       insertDynamicBuiltinNameDefinition dynamicTraceDefinitionMock $
       insertDynamicBuiltinNameDefinition dynamicCharToStringDefinition $
       insertDynamicBuiltinNameDefinition dynamicAppendDefinition mempty
