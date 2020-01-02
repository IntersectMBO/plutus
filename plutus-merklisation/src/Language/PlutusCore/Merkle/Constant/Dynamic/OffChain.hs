module Language.PlutusCore.Merkle.Constant.Dynamic.OffChain ( getStringBuiltinTypes ) where

import           Control.Monad.Except
import qualified Language.PlutusCore.Constant.Dynamic.OffChain as PLC
import           Language.PlutusCore.Error
import           Language.PlutusCore.Quote
import qualified Language.PlutusCore.TypeCheck                 as T

getStringBuiltinTypes
    :: (AsTypeError e ann, MonadError e m, MonadQuote m) => ann -> m T.DynamicBuiltinNameTypes
getStringBuiltinTypes ann =
    do
      coreTypes :: T.DynamicBuiltinNameTypes <- PLC.getStringBuiltinTypes ann
      return coreTypes
