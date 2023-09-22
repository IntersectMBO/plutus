{-# LANGUAGE KindSignatures  #-}
{-# LANGUAGE TemplateHaskell #-}
module PlutusIR.Analysis.Builtins where

import Control.Lens.TH
import Data.Kind
import PlutusCore.Builtin
import PlutusCore.Builtin qualified as PLC
import PlutusPrelude (Default (..))

-- | All non-static information about builtins that the compiler might want.
data BuiltinsInfo (uni :: Type -> Type) fun = BuiltinsInfo
  { _biSemanticsVariant :: PLC.BuiltinSemanticsVariant fun
  }

makeLenses ''BuiltinsInfo

instance (Default (BuiltinSemanticsVariant fun)) => Default (BuiltinsInfo uni fun) where
  def = BuiltinsInfo def
