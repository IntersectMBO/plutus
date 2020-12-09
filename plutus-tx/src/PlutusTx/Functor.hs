{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
module PlutusTx.Functor (Functor(..), (<$>), (<$), const, id) where

import           Control.Applicative   (Const (..))
import           Data.Functor.Identity (Identity (..))
import           Prelude               hiding (Functor (..), const, id, (<$), (<$>))

{-# ANN module ("HLint: ignore"::String) #-}

-- | Plutus Tx version of 'Data.Functor.Functor'.
class Functor f where
    -- | Plutus Tx version of 'Data.Functor.fmap'.
    fmap :: (a -> b) -> f a -> f b

    -- (<$) deliberately omitted, to make this a one-method class which has a
    -- simpler representation

infixl 4 <$>
-- | Plutus Tx version of '(Data.Functor.<$>)'.
{-# NOINLINE (<$>) #-}
(<$>) :: Functor f => (a -> b) -> f a -> f b
(<$>) f fa = fmap f fa

infixl 4 <$
{-# NOINLINE (<$) #-}
-- | Plutus Tx version of '(Data.Functor.<$)'.
(<$) :: Functor f => a -> f b -> f a
(<$) a fb = fmap (const a) fb

instance Functor [] where
    {-# NOINLINE fmap #-}
    fmap f l = case l of
            []   -> []
            x:xs -> f x : fmap f xs

instance Functor Maybe where
    {-# NOINLINE fmap #-}
    fmap f (Just a) = Just (f a)
    fmap _ Nothing  = Nothing

instance Functor (Either c) where
    {-# NOINLINE fmap #-}
    fmap f (Right a) = Right (f a)
    fmap _ (Left c)  = Left c

instance Functor ((,) c) where
    {-# NOINLINE fmap #-}
    fmap f (c, a) = (c, f a)

instance Functor Identity where
    {-# NOINLINE fmap #-}
    fmap f (Identity a) = Identity (f a)

instance Functor (Const m) where
    {-# NOINLINE fmap #-}
    fmap _ (Const c) = Const c

{-# NOINLINE const #-}
-- | Plutus Tx version of 'Prelude.const'.
const :: a -> b -> a
const x _ =  x

{-# NOINLINE id #-}
-- | Plutus Tx version of 'Prelude.id'.
id :: a -> a
id x = x
