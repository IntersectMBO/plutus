{-# LANGUAGE RankNTypes #-}

module PlutusCore.Builtin.Emitter
    ( ChurchList (..)
    , Emitter (..)
    , runEmitter
    , emit
    , forThen_
    ) where

import Control.Monad.Trans.Writer.Strict (Writer, runWriter, tell)
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

singletonChurchList :: a -> ChurchList a
singletonChurchList x = ChurchList ($ x)
{-# INLINE singletonChurchList #-}

forThen_ :: Applicative f => ChurchList a -> (a -> f ()) -> f b -> f b
forThen_ (ChurchList k) f = k c where
    c x z = f x *> z
    {-# INLINE c #-}

newtype Emitter a = Emitter
    { unEmitter :: Writer (ChurchList Text) a
    } deriving newtype (Functor, Applicative, Monad)

runEmitter :: Emitter a -> (a, ChurchList Text)
runEmitter = runWriter . unEmitter
{-# INLINE runEmitter #-}

emit :: Text -> Emitter ()
emit text = Emitter . tell $ singletonChurchList text
{-# INLINE emit #-}
