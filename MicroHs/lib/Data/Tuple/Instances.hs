module Data.Tuple.Instances where

-- Dubious instances for tuples

instance Functor ((,) a1) where
  fmap f (a1, a) = (a1, f a)

instance Functor ((,,) a1 a2) where
  fmap f (a1, a2, a) = (a1, a2, f a)

instance Functor ((,,,) a1 a2 a3) where
  fmap f (a1, a2, a3, a) = (a1, a2, a3, f a)

instance (Monoid a1) => Applicative ((,) a1) where
  pure a = (mempty, a)
  (a1, f) <*> (a1', a) = (a1 <> a1', f a)

instance (Monoid a1, Monoid a2) => Applicative ((,,) a1 a2) where
  pure a = (mempty, mempty, a)
  (a1, a2, f) <*> (a1', a2', a) = (a1 <> a1', a2 <> a2', f a)

instance (Monoid a1, Monoid a2, Monoid a3) => Applicative ((,,,) a1 a2 a3) where
  pure a = (mempty, mempty, mempty, a)
  (a1, a2, a3, f) <*> (a1', a2', a3', a) = (a1 <> a1', a2 <> a2', a3 <> a3', f a)

instance Monoid a1 => Monad ((,) a1) where
  (a1, a) >>= k = case k a of (a1', b) -> (a1 <> a1', b)

instance (Monoid a1, Monoid a2) => Monad ((,,) a1 a2) where
  (a1, a2, a) >>= k = case k a of (a1', a2', b) -> (a1 <> a1', a2 <> a2', b)

instance (Monoid a1, Monoid a2, Monoid a3) => Monad ((,,,) a1 a2 a3) where
  (a1, a2, a3, a) >>= k = case k a of (a1', a2', a3', b) -> (a1 <> a1', a2 <> a2', a3 <> a3', b)
