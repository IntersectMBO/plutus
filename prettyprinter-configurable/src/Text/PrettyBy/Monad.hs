{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE RankNTypes             #-}

module Text.PrettyBy.Monad where

import           Text.Pretty
import           Text.PrettyBy.Internal.Core

import           Control.Monad.Reader
import           Data.Functor.Const
import           Lens.Micro
import           Lens.Micro.Internal         (( #. ))

view :: MonadReader s m => Getting a s a -> m a
view l = asks (getConst #. l Const)
{-# INLINE view #-}

class HasPrettyConfig env config | env -> config where
    prettyConfig :: Lens' env config

type MonadPretty config env m = (MonadReader env m, HasPrettyConfig env config)

newtype Sole a = Sole
    { unSole :: a
    }

instance HasPrettyConfig (Sole config) config where
    prettyConfig f (Sole x) = Sole <$> f x

prettyM :: (MonadPretty config env m, PrettyBy config a) => a -> m (Doc ann)
prettyM x = flip prettyBy x <$> view prettyConfig
