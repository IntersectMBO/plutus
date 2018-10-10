module Language.PlutusCore.TypeSynthesis.Type ( TypeCheckM
                                              , TypeConfig (..)
                                              , TypeSt
                                              , TypeCheckSt (..)
                                              , TypeCheckCfg (..)
                                              -- * Lenses
                                              , uniqueLookup
                                              , gas
                                              , sizeToType
                                              -- * Helper functions
                                              , typeCheckStep
                                              ) where

import           Control.Monad.Except      (ExceptT, MonadError (throwError))
import           Control.Monad.Reader      (ReaderT)
import           Control.Monad.State       (StateT)
import           Control.Monad.State.Class (MonadState, get, modify)
import qualified Data.IntMap               as IM
import           Language.PlutusCore.Error
import           Language.PlutusCore.Quote
import           Language.PlutusCore.Type
import           Lens.Micro                (Lens', over)
import           PlutusPrelude

newtype TypeConfig = TypeConfig
    { _typeConfigNormalize :: Bool  -- ^ Whether we normalize type annotations
    }

type TypeSt = IM.IntMap (NormalizedType TyNameWithKind ())

data TypeCheckSt = TypeCheckSt
    { _uniqueLookup :: TypeSt
    , _gas          :: Natural
    }

data TypeCheckCfg = TypeCheckCfg
    { _cfgGas       :: Natural  -- ^ Gas to be provided to the typechecker
    , _cfgNormalize :: Bool     -- ^ Whether we should normalize type annotations
    }

-- | The type checking monad contains the 'BuiltinTable' and it lets us throw
-- 'TypeError's.
type TypeCheckM a = StateT TypeCheckSt (ReaderT TypeConfig (ExceptT (TypeError a) Quote))

uniqueLookup :: Lens' TypeCheckSt TypeSt
uniqueLookup f s = fmap (\x -> s { _uniqueLookup = x }) (f (_uniqueLookup s))

gas :: Lens' TypeCheckSt Natural
gas f s = fmap (\x -> s { _gas = x }) (f (_gas s))

sizeToType :: Kind ()
sizeToType = KindArrow () (Size ()) (Type ())

typeCheckStep :: (MonadState TypeCheckSt m, MonadError (TypeError a) m)
              => m ()
typeCheckStep = do
    (TypeCheckSt _ i) <- get
    if i == 0
        then throwError OutOfGas
        else modify (over gas (subtract 1))
