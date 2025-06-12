{-# LANGUAGE Safe #-}

-- |
--
-- Module      :  Control.Arrow
-- Copyright   :  (c) Ross Paterson 2002
-- License     :  BSD-style (see the LICENSE file in the distribution)
module Control.Arrow
    (-- *  Arrows
     Arrow(..),
     Kleisli(..),
     -- **  Derived combinators
     returnA,
     (^>>),
     (>>^),
     (>>>),
     (<<<),
     -- **  Right-to-left variants
     (<<^),
     (^<<),
     -- *  Monoid operations
     ArrowZero(..),
     ArrowPlus(..),
     -- *  Conditionals
     ArrowChoice(..),
     -- *  Arrow application
     ArrowApply(..),
     ArrowMonad(..),
     leftApp,
     -- *  Feedback
     ArrowLoop(..)
     ) where
import Control.Applicative
import Control.Category
import Control.Monad
import Control.Monad.Fix
import Prelude hiding (id, (.))

infixr 5 <+>
infixr 3 ***
infixr 3 &&&
infixr 2 +++
infixr 2 |||
infixr 1 ^>>, >>^
infixr 1 ^<<, <<^

class Category a => Arrow a where
    arr :: (b -> c) -> a b c
    first :: a b c -> a (b,d) (c,d)
    first = (*** id)
    second :: a b c -> a (d,b) (d,c)
    second = (id ***)
    (***) :: a b c -> a b' c' -> a (b,b') (c,c')
    f *** g = first f >>> arr swap >>> first g >>> arr swap
      where
        swap :: forall x y . (x, y) -> (y, x)
        swap ~(x,y) = (y,x)
    (&&&) :: a b c -> a b c' -> a b (c,c')
    f &&& g = arr (\b -> (b,b)) >>> f *** g

instance Arrow (->) where
    arr f = f
    (***) f g ~(x,y) = (f x, g y)

newtype Kleisli m a b = Kleisli { runKleisli :: a -> m b }

{-
deriving instance Generic (Kleisli m a b)

deriving instance Generic1 (Kleisli m a)

deriving instance Functor m => Functor (Kleisli m a)
-}
instance Functor m => Functor (Kleisli m a) where
  fmap f k = Kleisli (fmap f . runKleisli k)

instance Applicative m => Applicative (Kleisli m a) where
  pure = Kleisli . const . pure
  Kleisli f <*> Kleisli g = Kleisli $ \x -> f x <*> g x
  Kleisli f *> Kleisli g = Kleisli $ \x -> f x *> g x
  Kleisli f <* Kleisli g = Kleisli $ \x -> f x <* g x

instance Alternative m => Alternative (Kleisli m a) where
  empty = Kleisli $ const empty
  Kleisli f <|> Kleisli g = Kleisli $ \x -> f x <|> g x

instance Monad m => Monad (Kleisli m a) where
  Kleisli f >>= k = Kleisli $ \x -> f x >>= \a -> runKleisli (k a) x

instance MonadPlus m => MonadPlus (Kleisli m a) where
  mzero = Kleisli $ const mzero
  Kleisli f `mplus` Kleisli g = Kleisli $ \x -> f x `mplus` g x

instance Monad m => Category (Kleisli m) where
    id = Kleisli return
    Kleisli f . Kleisli g = Kleisli (g >=> f)

instance Monad m => Arrow (Kleisli m) where
    arr f = Kleisli (return . f)
    first (Kleisli f) = Kleisli (\ ~(b,d) -> f b >>= \c -> return (c,d))
    second (Kleisli f) = Kleisli (\ ~(d,b) -> f b >>= \c -> return (d,c))

returnA :: Arrow a => a b b
returnA = id

(^>>) :: Arrow a => (b -> c) -> a c d -> a b d
f ^>> a = arr f >>> a

(>>^) :: Arrow a => a b c -> (c -> d) -> a b d
a >>^ f = a >>> arr f

(<<^) :: Arrow a => a c d -> (b -> c) -> a b d
a <<^ f = a <<< arr f

(^<<) :: Arrow a => (c -> d) -> a b c -> a b d
f ^<< a = arr f <<< a

class Arrow a => ArrowZero a where
    zeroArrow :: a b c

instance MonadPlus m => ArrowZero (Kleisli m) where
    zeroArrow = Kleisli (const mzero)

class ArrowZero a => ArrowPlus a where
    (<+>) :: a b c -> a b c -> a b c

instance MonadPlus m => ArrowPlus (Kleisli m) where
    Kleisli f <+> Kleisli g = Kleisli (\x -> f x `mplus` g x)

class Arrow a => ArrowChoice a where
    left :: a b c -> a (Either b d) (Either c d)
    left = (+++ id)
    right :: a b c -> a (Either d b) (Either d c)
    right = (id +++)
    (+++) :: a b c -> a b' c' -> a (Either b b') (Either c c')
    f +++ g = left f >>> arr mirror >>> left g >>> arr mirror
      where
        mirror :: Either x y -> Either y x
        mirror (Left x)  = Right x
        mirror (Right y) = Left y
    (|||) :: a b d -> a c d -> a (Either b c) d
    f ||| g = f +++ g >>> arr untag
      where
        untag (Left x)  = x
        untag (Right y) = y

instance ArrowChoice (->) where
    left f = f +++ id
    right f = id +++ f
    f +++ g = (Left . f) ||| (Right . g)
    (|||) = either

instance Monad m => ArrowChoice (Kleisli m) where
    left f = f +++ arr id
    right f = arr id +++ f
    f +++ g = (f >>> arr Left) ||| (g >>> arr Right)
    Kleisli f ||| Kleisli g = Kleisli (either f g)

class Arrow a => ArrowApply a where
    app :: a (a b c, b) c

instance ArrowApply (->) where
    app (f,x) = f x

instance Monad m => ArrowApply (Kleisli m) where
    app = Kleisli (\(Kleisli f, x) -> f x)

newtype ArrowMonad a b = ArrowMonad (a () b)

instance Arrow a => Functor (ArrowMonad a) where
    fmap f (ArrowMonad m) = ArrowMonad $ m >>> arr f

instance Arrow a => Applicative (ArrowMonad a) where
   pure x = ArrowMonad (arr (const x))
   ArrowMonad f <*> ArrowMonad x = ArrowMonad (f &&& x >>> arr (uncurry id))

instance ArrowApply a => Monad (ArrowMonad a) where
    ArrowMonad m >>= f = ArrowMonad $
        m >>> arr (\x -> let ArrowMonad h = f x in (h, ())) >>> app

instance ArrowPlus a => Alternative (ArrowMonad a) where
   empty = ArrowMonad zeroArrow
   ArrowMonad x <|> ArrowMonad y = ArrowMonad (x <+> y)

instance (ArrowApply a, ArrowPlus a) => MonadPlus (ArrowMonad a)

leftApp :: ArrowApply a => a b c -> a (Either b d) (Either c d)
leftApp f = arr ((\b -> (arr (\() -> b) >>> f >>> arr Left, ())) |||
             (\d -> (arr (\() -> d) >>> arr Right, ()))) >>> app

class Arrow a => ArrowLoop a where
    loop :: a (b,d) (c,d) -> a b c

instance ArrowLoop (->) where
    loop f b = let (c,d) = f (b,d) in c

instance MonadFix m => ArrowLoop (Kleisli m) where
    loop (Kleisli f) = Kleisli (fmap fst . mfix . f')
      where f' x y = f (x, snd y)
