{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
module Foundation.Monad
    ( MonadIO(..)
    , MonadFailure(..)
    , MonadThrow(..)
    , MonadCatch(..)
    , MonadBracket(..)
    , MonadTrans(..)
    , Identity(..)
    , replicateM
    ) where

import Basement.Imports
import Basement.Types.OffsetSize
import Basement.Monad (MonadFailure(..))
import Foundation.Monad.MonadIO
import Foundation.Monad.Exception
import Foundation.Monad.Transformer
import Foundation.Numerical
import Control.Applicative (liftA2)

#if MIN_VERSION_base(4,8,0)
import Data.Functor.Identity

#else

import Control.Monad.Fix
import Control.Monad.Zip
import Basement.Compat.Base

import GHC.Generics (Generic1)

-- | Identity functor and monad. (a non-strict monad)
--
-- @since 4.8.0.0
newtype Identity a = Identity { runIdentity :: a }
    deriving (Eq, Ord, Data, Generic, Generic1, Typeable)

instance Functor Identity where
    fmap f (Identity x) = Identity (f x)

instance Applicative Identity where
    pure     = Identity
    Identity f <*> Identity x = Identity (f x)

instance Monad Identity where
    return   = Identity
    m >>= k  = k (runIdentity m)

instance MonadFix Identity where
    mfix f   = Identity (fix (runIdentity . f))

instance MonadZip Identity where
    mzipWith f (Identity x) (Identity y) = Identity (f x y)
    munzip (Identity (x, y)) = (Identity x, Identity y)

#endif

-- | @'replicateM' n act@ performs the action @n@ times,
-- gathering the results.
replicateM :: Applicative m => CountOf a -> m a -> m [a]
replicateM (CountOf count) f = loop count
  where
    loop cnt
        | cnt <= 0  = pure []
        | otherwise = liftA2 (:) f (loop (cnt - 1))
{-# INLINEABLE replicateM #-}
