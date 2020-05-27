{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE RankNTypes             #-}

module Text.PrettyBy.Monad
    ( HasPrettyConfig (..)
    , MonadPretty
    , Sole (..)
    , prettyM
    ) where

import           Text.Pretty
import           Text.PrettyBy.Internal
import           Text.PrettyBy.Internal.Utils

import           Control.Monad.Reader
import           Lens.Micro

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
