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
    , displayM
    ) where

import           Text.Pretty
import           Text.PrettyBy.Default
import           Text.PrettyBy.Internal
import           Text.PrettyBy.Internal.Utils

import           Control.Monad.Reader
import           Lens.Micro

-- | A constraint for \"@config@ is a part of @env@\".
class HasPrettyConfig env config | env -> config where
    prettyConfig :: Lens' env config

-- @env@ is an artifact of the encoding, it shouldn't be necessary as @m@ determines what it is
-- and we're not interested in reflecting @env@ explicitly (unlike @config@, which is also
-- determined by @m@ through @env@, but is useful to have explicitly). But GHC does not like it
-- when @env@ is left implicit, see https://gitlab.haskell.org/ghc/ghc/issues/3490
-- | A constraint for \"@m@ is a monad that allows to pretty-print values in it by a @config@\".
type MonadPretty config env m = (MonadReader env m, HasPrettyConfig env config)

-- | A @newtype@ wrapper around @a@ introduced for its 'HasPrettyConfig' instance.
newtype Sole a = Sole
    { unSole :: a
    }

instance HasPrettyConfig (Sole config) config where
    prettyConfig f (Sole x) = Sole <$> f x

prettyM :: (MonadPretty config env m, PrettyBy config a) => a -> m (Doc ann)
prettyM x = flip prettyBy x <$> view prettyConfig

-- | Render a value as 'String'.
displayM
    :: forall str a m env config. (MonadPretty config env m, PrettyBy config a, Render str)
    => a -> m str
displayM = fmap render . prettyM
