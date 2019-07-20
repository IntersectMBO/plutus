{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}
module Recursion where

import           Data.Functor.Identity

import           IFix

newtype SelfF f a = SelfF (f a -> a)
-- | Values that can be applied to themselves.
type Self a = IFix SelfF a

-- Some of these need to be NOINLINE to prevent a known
-- loop in GHC's simplifier!

{-# NOINLINE self #-}
self :: forall a . (Self a -> a) -> Self a
self f = Wrap $ SelfF f

{-# NOINLINE unself #-}
unself :: forall a . Self a -> Self a -> a
unself (Wrap (SelfF s)) = s

{-# NOINLINE selfApply #-}
selfApply :: forall a . Self a -> a
selfApply s = unself s s

z :: forall a b . ((a -> b) -> (a -> b)) -> (a -> b)
z f = let a r = f (\x -> selfApply r x) in a (self a)

infixr 0 $$
-- | Natural transformation. Reified to aid GHC's type inference.
newtype f ~> g = NT { ($$) :: forall q . f q -> g q }

(<.>) :: (b ~> c) -> (a ~> b) -> (a ~> c)
NT f <.> NT g = NT (f . g)

fixBy :: forall f .
    ((f ~> Identity) -> (f ~> Identity)) ->
    ((f ~> f) -> (f ~> Identity))
fixBy by = z rr where
    rr :: ((f ~> f) -> (f ~> Identity)) -> ((f ~> f) -> (f ~> Identity))
    rr r g = by (r g) <.> g

-- | Named type representing '\b . a -> b'. Reified to aid GHC's type inference.
newtype Arr a b = Arr (a -> b)
-- | Named type representing '\c . a -> b -> c'. Reified to aid GHC's type inference.
newtype ArrArr a b c = ArrArr (a -> b -> c)

by1z :: forall a1 b1 . (Arr (a1 -> b1) ~> Identity) -> (Arr (a1 -> b1) ~> Identity)
by1z r = NT $ \(Arr k) -> Identity $ k
    (\x -> runIdentity $ r $$ Arr (\f1 -> f1 x))

fix1z :: forall a1 b1 . (Arr (a1 -> b1) ~> Arr (a1 -> b1)) -> (Arr (a1 -> b1) ~> Identity)
fix1z = fixBy by1z

fix1zSimple :: forall a b . ((a -> b) -> (a -> b)) -> (a -> b)
fix1zSimple selfImpl a = runIdentity $ nt $$ Arr $ \f -> f a
    where
        nt :: Arr (a -> b) ~> Identity
        nt = fix1z $ NT $ \(Arr sel) -> Arr $ \r -> sel $ selfImpl r

by2z :: forall a1 b1 a2 b2 . (ArrArr (a1 -> b1) (a2 -> b2) ~> Identity) -> (ArrArr (a1 -> b1) (a2 -> b2) ~> Identity)
by2z r = NT $ \(ArrArr k) -> Identity $ k
    (\x -> runIdentity $ r $$ ArrArr (\f1 _f2 -> f1 x))
    (\x -> runIdentity $ r $$ ArrArr (\_f1 f2 -> f2 x))

fix2z :: forall a1 b1 a2 b2 . (ArrArr (a1 -> b1) (a2 -> b2) ~> ArrArr (a1 -> b1) (a2 -> b2)) -> (ArrArr (a1 -> b1) (a2 -> b2) ~> Identity)
fix2z = fixBy by2z
