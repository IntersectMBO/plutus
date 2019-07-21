module Language.PlutusCore.Constant.Dynamic.OffChain
    ( getStringBuiltinTypes
    ) where

import           Control.Monad.Except
import           Language.PlutusCore.Constant.Dynamic.BuiltinName
import           Language.PlutusCore.Constant.Function
import           Language.PlutusCore.Constant.Typed
import           Language.PlutusCore.Error
import           Language.PlutusCore.Quote
import           Language.PlutusCore.TypeCheck

getStringBuiltinTypes
    :: (AsTypeError e uni ann, MonadError e m, MonadQuote m, Evaluable uni)
    => ann -> m (DynamicBuiltinNameTypes uni)
getStringBuiltinTypes ann =
       dynamicBuiltinNameMeaningsToTypes ann $
       insertDynamicBuiltinNameDefinition dynamicTraceDefinitionMock $
       insertDynamicBuiltinNameDefinition dynamicCharToStringDefinition $
       insertDynamicBuiltinNameDefinition dynamicAppendDefinition mempty
