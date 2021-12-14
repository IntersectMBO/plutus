{-# LANGUAGE ConstraintKinds #-}
module Foundation.Monad.Transformer
    ( MonadTrans(..)
    ) where

import Basement.Compat.Base (Monad)

-- | Basic Transformer class
class MonadTrans trans where
    -- | Lift a computation from an inner monad to the current transformer monad
    lift :: Monad m => m a -> trans m a
