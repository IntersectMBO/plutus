{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE Rank2Types            #-}
module Ledger.Typed.TypeUtils where

import           Data.Kind
import           Data.Proxy

-- | A heterogeneous list where every element is wrapped with the given functor.
data HListF (f :: Type -> Type) (l :: [Type]) where
    HNilF  :: HListF f '[]
    HConsF :: f e -> HListF f l -> HListF f (e ': l)

-- | Turn a 'HListF' into a homogeneous list. Requires a very polymorphic function, likely something like 'coerce'.
hfOut :: forall o f (ts :: [Type]) . (forall a . f a -> o) -> HListF f ts -> [o]
hfOut _ HNilF = []
hfOut f (HConsF e es) = f e : hfOut f es

-- Type-level lists

-- | Assert that a constraint holds for all types in a type-level list.
type family All (c :: Type -> Constraint) (ts :: [Type]) :: Constraint where
    All c '[] = ()
    All c (t ': ts) = (c t, All c ts)

-- | Transforms a @[t]@ and @r@ into @t1 -> ... -> tn -> r@.
type family Uncurry (l :: [Type]) r where
    Uncurry '[] r = r
    Uncurry (x ': xs) r = x -> Uncurry xs r

-- Defunctionalization
-- Mostly lifted from singletons

data TyFun :: Type -> Type -> Type

type a ~> b = TyFun a b -> Type

type family Apply (f :: k1 ~> k2) (x :: k1) :: k2

type family Map (f :: k1 ~> k2) (l :: [k1]) :: [k2] where
    Map f '[] = '[]
    Map f (x ': xs) = Apply f x ': Map f xs

-- List spine witnesses

data Spine (ts :: [Type]) where
    NilSpine :: Spine '[]
    ConsSpine :: Spine xs -> Spine (x ': xs)

mapSpine :: Proxy f -> Spine ts -> Spine (Map f ts)
mapSpine _ NilSpine = NilSpine
mapSpine p (ConsSpine sp) = ConsSpine (mapSpine p sp)

class KnownSpine (ts :: [Type]) where
    spine :: Spine ts

instance KnownSpine '[] where
    spine = NilSpine

instance KnownSpine xs => KnownSpine (x ': xs) where
    spine = ConsSpine spine
