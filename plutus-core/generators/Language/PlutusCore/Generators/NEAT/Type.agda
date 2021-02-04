module Language.PlutusCore.Generators.NEAT.Type where

{-# FOREIGN AGDA2HS
{-# OPTIONS_GHC -fno-warn-orphans      #-}
{-# LANGUAGE DeriveAnyClass            #-}
{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE DerivingVia               #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE OverloadedStrings         #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE StandaloneDeriving        #-}

import           Control.Enumerable
import           Language.PlutusCore
import           Language.PlutusCore.Generators.NEAT.Common

#-}

open import Relation.Binary.PropositionalEquality
open import Haskell.Prelude hiding (m)
open import Language.PlutusCore.Generators.NEAT.Common

{-# FOREIGN AGDA2HS
newtype Neutral a = Neutral
  { unNeutral :: a
  }
#-}
-- * Enumeration

-- ** Enumerating types

data TypeBuiltinG : Set where
  TyByteStringG  : TypeBuiltinG
  TyIntegerG     : TypeBuiltinG
  TyStringG      : TypeBuiltinG
  TyBoolG        : TypeBuiltinG
  TyUnitG        : TypeBuiltinG
  TyCharG        : TypeBuiltinG 


{-# COMPILE AGDA2HS TypeBuiltinG deriving (Show, Eq, Ord) #-}

{-# FOREIGN AGDA2HS
deriveEnumerable ''TypeBuiltinG
#-}

-- NOTE: Unusually, the application case is annotated with a kind.
--       The reason is eagerness and efficiency. If we have the kind
--       information at the application site, we can check the two
--       subterms in parallel, while evaluating as little as possible.

variable
  n m o : Set

postulate Kind : Set → Set

data TypeG (n : Set) : Set where
  TyVarG : n → TypeG n
  TyFunG : TypeG n → TypeG n → TypeG n
  TyIFixG : TypeG n  → Kind ⊤ → TypeG n → TypeG n
  TyForallG : Kind ⊤ → TypeG (S n) → TypeG n
  TyBuiltinG : TypeBuiltinG → TypeG n
  TyLamG : TypeG (S n) → TypeG n
  TyAppG : TypeG n → TypeG n → Kind ⊤ → TypeG n

{-# COMPILE AGDA2HS TypeG deriving (Typeable, Eq, Ord, Show) #-}

{-# FOREIGN AGDA2HS
deriving instance Ord (Kind ())

deriveEnumerable ''Kind

deriveEnumerable ''TypeG

type ClosedTypeG = TypeG Z

instance Functor TypeG where
  fmap = ren
#-}

ext : (m → n) → S m → S n
ext _ FZ     = FZ
ext f (FS x) = FS (f x)

{-# COMPILE AGDA2HS ext #-}

ren : (m → n) → TypeG m → TypeG n
ren f (TyVarG x) = TyVarG (f x)
ren f (TyFunG ty1 ty2) = TyFunG (ren f ty1) (ren f ty2)
ren f (TyIFixG ty1 k ty2) = TyIFixG (ren f ty1) k (ren f ty2)
ren f (TyForallG k ty) = TyForallG k (ren (ext f) ty)
ren _ (TyBuiltinG b) = TyBuiltinG b
ren f (TyLamG ty) = TyLamG (ren (ext f) ty)
ren f (TyAppG ty1 ty2 k) = TyAppG (ren f ty1) (ren f ty2) k

{-# COMPILE AGDA2HS ren #-}

ext-cong : {f g : m → n} → (∀ x → f x ≡ g x) → ∀ x → ext f x ≡ ext g x
ext-cong p FZ     = refl
ext-cong p (FS x) = cong FS (p x)

ren-cong : {f g : m → n} → (∀ x → f x ≡ g x) → ∀ t → ren f t ≡ ren g t
ren-cong p (TyVarG x)          = cong TyVarG (p x)
ren-cong p (TyFunG ty1 ty2)    = cong₂ TyFunG (ren-cong p ty1) (ren-cong p ty2)
ren-cong p (TyIFixG ty1 k ty2) =
  cong₂ (λ ty1 ty2 → TyIFixG ty1 k ty2) (ren-cong p ty1) (ren-cong p ty2)
ren-cong p (TyForallG k ty)    = cong (TyForallG k) (ren-cong (ext-cong p) ty)
ren-cong p (TyBuiltinG b)      = refl
ren-cong p (TyLamG ty)         = cong TyLamG (ren-cong (ext-cong p) ty)
ren-cong p (TyAppG ty1 ty2 k)  =
  cong₂ (λ ty1 ty2 → TyAppG ty1 ty2 k) (ren-cong p ty1) (ren-cong p ty2)

-- ext (map for S) satisfies the functor laws

ext-id : (x : S m) → ext id x ≡ x
ext-id FZ     = refl
ext-id (FS x) = refl

ext-comp : (x : S m)(σ : m → n)(σ' : n → o) → ext (σ' ∘ σ) x ≡ ext σ' (ext σ x)
ext-comp FZ     σ σ' = refl
ext-comp (FS x) σ σ' = refl

-- ren (map for TypeG) satisfies the functor laws

ren-id : (ty : TypeG m) → ren id ty ≡ ty 
ren-id (TyVarG _)          = refl
ren-id (TyFunG ty1 ty2)    = cong₂ TyFunG (ren-id ty1) (ren-id ty2)
ren-id (TyIFixG ty1 k ty2) =
  cong₂ (λ ty1 ty2 → TyIFixG ty1 k ty2) (ren-id ty1) (ren-id ty2)
ren-id (TyForallG k ty)    =
  cong (TyForallG k) (trans (ren-cong ext-id ty) (ren-id ty))
ren-id (TyBuiltinG _)      = refl
ren-id (TyLamG ty)         =
  cong TyLamG (trans (ren-cong ext-id ty) (ren-id ty))
ren-id (TyAppG ty1 ty2 k)  =
  cong₂ (λ ty1 ty2 → TyAppG ty1 ty2 k) (ren-id ty1) (ren-id ty2)

ren-comp : (ty : TypeG m)(σ : m → n)(σ' : n → o)
         → ren (σ' ∘ σ) ty ≡ ren σ' (ren σ ty)
ren-comp (TyVarG x)          σ σ' = refl
ren-comp (TyFunG ty1 ty2)    σ σ' =
  cong₂ TyFunG (ren-comp ty1 σ σ') (ren-comp ty2 σ σ')
ren-comp (TyIFixG ty1 k ty2) σ σ' =
  cong₂ (λ ty1 ty2 → TyIFixG ty1 k ty2) (ren-comp ty1 σ σ') (ren-comp ty2 σ σ')
ren-comp (TyForallG k ty)    σ σ' = cong
  (TyForallG k)
  (trans (ren-cong (λ x → ext-comp x σ σ') ty)
         (ren-comp ty (ext σ) (ext σ')))
ren-comp (TyBuiltinG b)      σ σ' = refl
ren-comp (TyLamG ty)         σ σ' = cong
  TyLamG
  (trans (ren-cong (λ x → ext-comp x σ σ') ty)
         (ren-comp ty (ext σ) (ext σ')))
ren-comp (TyAppG ty1 ty2 k)  σ σ' =
  cong₂ (λ ty1 ty2 → TyAppG ty1 ty2 k) (ren-comp ty1 σ σ') (ren-comp ty2 σ σ')
