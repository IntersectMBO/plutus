{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE RankNTypes             #-}

module Text.PrettyBy.Monad where

import           Text.PrettyBy.Internal.Core

import           Control.Monad.Reader
import           Data.Functor.Const
import           Lens.Micro
import           Lens.Micro.Internal         (( #. ))
import           Text.Pretty

view :: MonadReader s m => Getting a s a -> m a
view l = asks (getConst #. l Const)
{-# INLINE view #-}

class HasPrettyConfig env config | env -> config where
    prettyConfig :: Lens' env config

type MonadPretty config env m = (MonadReader env m, HasPrettyConfig env config)

prettyM :: (MonadPretty config env m, PrettyBy config a) => a -> m (Doc ann)
prettyM x = flip prettyBy x <$> view prettyConfig

newtype Sole a = Sole
    { unSole :: a
    }

instance HasPrettyConfig (Sole config) config where
    prettyConfig f (Sole x) = Sole <$> f x

viaPrettyM :: (a -> Reader (Sole config) (Doc ann)) -> config -> a -> Doc ann
viaPrettyM pM config x = runReader (pM x) $ Sole config
