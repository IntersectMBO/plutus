{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module PlutusTx.Blueprint.Definition.TF where

import Data.Kind (Type)
import GHC.Generics (K1, M1, U1, type (:*:), type (:+:))

----------------------------------------------------------------------------------------------------
-- Detect stuck type families: https://blog.csongor.co.uk/report-stuck-families/#custom-type-errors

type family IfStuckUnroll (e :: [Type]) (t :: [Type]) :: [Type] where
  IfStuckUnroll _ '[] = '[]
  IfStuckUnroll _ (x ': xs) = (x ': xs)
  IfStuckUnroll e _ = e

type family IfStuckRep e (rep :: Type -> Type) :: Type -> Type where
  IfStuckRep _ (M1 a b c) = M1 a b c
  IfStuckRep _ (f :*: g) = f :*: g
  IfStuckRep _ (f :+: g) = f :+: g
  IfStuckRep _ (K1 a b) = K1 a b
  IfStuckRep e U1 = U1
  IfStuckRep e x = e

----------------------------------------------------------------------------------------------------
-- Type-level list operations ----------------------------------------------------------------------

-- | Insert @x@ into @xs@ unless it's already there.
type Insert :: forall k. k -> [k] -> [k]
type family Insert x xs where
  Insert x '[] = '[x]
  Insert x (x : xs) = x ': xs
  Insert x (y : xs) = y ': Insert x xs

-- | Concatenates two type-level lists
type Concat :: forall k. [k] -> [k] -> [k]
type family Concat (as :: [k]) (bs :: [k]) :: [k] where
  Concat '[] bs = bs
  Concat as '[] = as
  Concat (a : as) bs = a ': Concat as bs

-- | Concatenates two type-level lists removing duplicates.
type (++) :: forall k. [k] -> [k] -> [k]
type family (as :: [k]) ++ (bs :: [k]) :: [k] where
  '[] ++ bs = bs
  as ++ '[] = as
  (a : as) ++ bs = Insert a (as ++ bs)

infixr 5 ++

type family Reverse (xs :: [k]) :: [k] where
  Reverse '[] = '[]
  Reverse (x ': xs) = Append (Reverse xs) '[x]

type family Append (xs :: [k]) (ys :: [k]) :: [k] where
  Append '[] ys = ys
  Append (x ': xs) ys = x ': Append xs ys

type family Nub xs where
  Nub xs = NubHelper '[] xs

type family NubHelper acc xs where
  NubHelper acc '[] = acc
  NubHelper acc (x ': xs) = NubHelper (Insert x acc) xs
