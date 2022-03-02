{-# LANGUAGE RankNTypes #-}

module PlutusCore.Builtin.Emitter
    ( ChurchList (..)
    , Emitter (..)
    , runEmitter
    , emit
    ) where

import Control.Monad.Writer.Strict
import Data.Text (Text)

newtype ChurchList a = ChurchList
    { unChurchList :: forall r. (a -> r -> r) -> r -> r
    }

instance Semigroup (ChurchList a) where
    ChurchList k1 <> ChurchList k2 = ChurchList $ \f -> k1 f . k2 f
    {-# INLINE (<>) #-}

instance Monoid (ChurchList a) where
    mempty = ChurchList $ \_ -> id
    {-# INLINE mempty #-}

instance Foldable ChurchList where
    foldr f z (ChurchList k) = k f z
    {-# INLINE foldr #-}

singletonChurchList :: a -> ChurchList a
singletonChurchList x = ChurchList ($ x)
{-# INLINE singletonChurchList #-}

newtype Emitter a = Emitter
    { unEmitter :: Writer (ChurchList Text) a
    } deriving newtype (Functor, Applicative, Monad)

runEmitter :: Emitter a -> (a, ChurchList Text)
runEmitter = runWriter . unEmitter
{-# INLINE runEmitter #-}

emit :: Text -> Emitter ()
emit text = Emitter . tell $ singletonChurchList text
{-# INLINE emit #-}
