{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE Rank2Types            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
module Ledger.Typed.TypeUtils where

import           Data.Kind

data Any

-- | A heterogeneous list where every element is wrapped with the given functor.
data HListF (f :: Type -> Type) (l :: [Type]) where
    HNilF  :: HListF f '[]
    HConsF :: f e -> HListF f l -> HListF f (e ': l)

-- | Turn a 'HListF' into a homogeneous list. Requires a very polymorphic function, likely something like 'coerce'.
hfOut :: forall o f (ts :: [Type]) . (forall a . f a -> o) -> HListF f ts -> [o]
hfOut _ HNilF         = []
hfOut f (HConsF e es) = f e : hfOut f es
