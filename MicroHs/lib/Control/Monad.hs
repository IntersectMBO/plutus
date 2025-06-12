-- Copyright 2023 Lennart Augustsson
-- See LICENSE file for full license.
module Control.Monad(
  Functor(..),
  Monad(..),
  MonadPlus(..),
  mapM,
  mapM_,
  forM,
  forM_,
  sequence,
  sequence_,
  (=<<),
  (>=>),
  (<=<),
  forever,
  void,
  join,
  msum,
  mfilter,
  filterM,
  mapAndUnzipM,
  zipWithM,
  zipWithM_,
  foldM,
  foldM_,
  replicateM,
  replicateM_,
  guard,
  when,
  unless,
  liftM,
  liftM2,
  liftM3,
  liftM4,
  liftM5,
  ap,
  ) where
import Control.Applicative
import Control.Error
import Data.Bool
import Data.Char_Type
import Data.Function
import Data.Functor hiding (unzip)
import Data.List
import Data.Monoid.Internal
import Data.Ord
import Prelude qualified ()
import Primitives
--import Data.Maybe

infixl 1 >>, >>=, =<<
infixr 1 <=<, >=>

class (Applicative m) => Monad m where
  (>>=)  :: forall a b . m a -> (a -> m b) -> m b
  (>>)   :: forall a b . m a -> m b -> m b
  ma >> mb = ma >>= const mb

  -- Maybe remove this
  return :: forall a . a -> m a
  return = pure

-----

mapM :: forall m a b . Monad m => (a -> m b) -> [a] -> m [b]
mapM f =
  let
    rec arg =
      case arg of
        [] -> return []
        a : as -> do
          b <- f a
          bs <- rec as
          return (b : bs)
  in rec

mapM_ :: forall m a b . Monad m => (a -> m b) -> [a] -> m ()
mapM_ f =
  let
    rec arg =
      case arg of
        [] -> return ()
        a : as -> do
          _ <- f a
          rec as
  in rec

forM :: forall m a b . Monad m => [a] -> (a -> m b) -> m [b]
forM = flip mapM

forM_ :: forall m a b . Monad m => [a] -> (a -> m b) -> m ()
forM_ = flip mapM_

sequence :: forall m a . Monad m => [m a] -> m [a]
sequence = mapM id

sequence_ :: forall m a . Monad m => [m a] -> m ()
sequence_ = mapM_ id

(=<<) :: forall m a b . Monad m => (a -> m b) -> m a -> m b
(=<<) = flip (>>=)

(<=<) :: forall m a b c . Monad m => (b -> m c) -> (a -> m b) -> (a -> m c)
f <=< g = \ a -> do
  b <- g a
  f b

(>=>) :: forall m a b c . Monad m => (a -> m b) -> (b -> m c) -> (a -> m c)
(>=>) = flip (<=<)

forever :: forall f a b . (Applicative f) => f a -> f b
forever a = let { a' = a *> a' } in a'

-----

join :: forall m a . (Monad m) => m (m a) -> m a
join x = x >>= id

filterM :: forall m a . Applicative m => (a -> m Bool) -> [a] -> m [a]
filterM _ []       = pure []
filterM p (x : xs) = liftA2 (\ flg -> if flg then (x:) else id) (p x) (filterM p xs)

-- XXX could relax some Monad to Applicative
mapAndUnzipM  :: forall m a b c . (Monad m) => (a -> m (b,c)) -> [a] -> m ([b], [c])
mapAndUnzipM f xs = unzip <$> mapM f xs

zipWithM :: forall m a b c . (Monad m) => (a -> b -> m c) -> [a] -> [b] -> m [c]
zipWithM f xs ys = sequence (zipWith f xs ys)

zipWithM_ :: forall m a b c . (Monad m) => (a -> b -> m c) -> [a] -> [b] -> m ()
zipWithM_ f xs ys = sequence_ (zipWith f xs ys)

foldM :: forall m a b . (Monad m) => (b -> a -> m b) -> b -> [a] -> m b
foldM = foldlM

foldM_ :: forall m a b . (Monad m) => (b -> a -> m b) -> b -> [a] -> m ()
foldM_ f a xs  = void (foldlM f a xs)

foldlM :: forall m a b . (Monad m) => (b -> a -> m b) -> b -> [a] -> m b
foldlM _ z [] = pure z
foldlM f z (x : xs) = do
  z' <- f z x
  foldlM f z' xs

replicateM  :: forall m a . (Applicative m) => Int -> m a -> m [a]
replicateM cnt0 f = loop cnt0
  where
    loop cnt =
      if cnt <= (0::Int) then pure []
      else liftA2 (:) f (loop (cnt `primIntSub` 1))

replicateM_  :: forall m a . (Applicative m) => Int -> m a -> m ()
replicateM_ cnt0 f = loop cnt0
  where
    loop cnt =
      if cnt <= (0::Int) then pure ()
      else f *> loop (cnt `primIntSub` 1)

-----

when :: forall m . Applicative m => Bool -> m () -> m ()
when p ma = if p then ma else pure ()

unless :: forall m . Applicative m => Bool -> m () -> m ()
unless p ma = if p then pure () else ma

-----

liftM :: forall m r a1 . (Monad m) => (a1 -> r) -> m a1 -> m r
liftM f m1 = f <$> m1
liftM2 :: forall m r a1 a2 . (Monad m) => (a1 -> a2 -> r) -> m a1 -> m a2 -> m r
liftM2 f m1 m2 = do { x1 <- m1; x2 <- m2; return (f x1 x2) }
liftM3 :: forall m r a1 a2 a3 . (Monad m) => (a1 -> a2 -> a3 -> r) -> m a1 -> m a2 -> m a3 -> m r
liftM3 f m1 m2 m3 = do { x1 <- m1; x2 <- m2; x3 <- m3; return (f x1 x2 x3) }
liftM4 :: forall m r a1 a2 a3 a4 . (Monad m) => (a1 -> a2 -> a3 -> a4 -> r) -> m a1 -> m a2 -> m a3 -> m a4 -> m r
liftM4 f m1 m2 m3 m4 = do { x1 <- m1; x2 <- m2; x3 <- m3; x4 <- m4; return (f x1 x2 x3 x4) }
liftM5 :: forall m r a1 a2 a3 a4 a5 . (Monad m) => (a1 -> a2 -> a3 -> a4 -> a5 -> r) -> m a1 -> m a2 -> m a3 -> m a4 -> m a5 -> m r
liftM5 f m1 m2 m3 m4 m5 = do { x1 <- m1; x2 <- m2; x3 <- m3; x4 <- m4; x5 <- m5; return (f x1 x2 x3 x4 x5) }

ap :: forall m a b . Monad m => m (a -> b) -> m a -> m b
ap f a = do
  f' <- f
  a' <- a
  return (f' a')

-----

instance Functor ((->) a) where
  fmap = (.)

instance Applicative ((->) a) where
  pure = const
  f <*> g = \ a -> f a (g a)

instance Monad ((->) a) where
  x >>= y = \ z -> y (x z) z

instance Monad Dual where
  m >>= k = k (getDual m)

instance Monad [] where
  (>>=) = flip concatMap

{-
-- Same for Maybe
instance Functor Maybe where
  fmap _ Nothing = Nothing
  fmap f (Just a) = Just (f a)

instance Applicative Maybe where
  pure a = Just a
  (<*>) = ap

instance Monad Maybe where
  Nothing >>= _ = Nothing
  Just a  >>= f = f a
-}

class (Alternative m, Monad m) => MonadPlus m where
  mzero :: forall a . m a
  mzero = empty
  mplus :: forall a . m a -> m a -> m a
  mplus = (<|>)

instance MonadPlus [] where
  mzero = []
  mplus = (++)

msum :: forall m a . (MonadPlus m) => [m a] -> m a
msum = foldr mplus mzero

mfilter :: forall m a . (MonadPlus m) => (a -> Bool) -> m a -> m a
mfilter p ma = do
  a <- ma
  if p a then return a else mzero
