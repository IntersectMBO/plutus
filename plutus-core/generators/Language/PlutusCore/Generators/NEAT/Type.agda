{-| Description: PLC Syntax, typechecker,semantics property based testing.

This file contains
1. A duplicate of the Plutus Core Abstract Syntax (types and terms)
2. A kind checker and a type checker
3. Reduction semantics for types
-}


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

import           Control.Enumerable
import           Control.Monad.Except
import           Data.Bifunctor.TH
import           Data.Coolean                               (Cool, false, toCool, true, (&&&))
import qualified Data.Stream                                as Stream
import qualified Data.Text                                  as Text
import           Language.PlutusCore
import           Language.PlutusCore.Generators.NEAT.Common
import           Text.Printf

#-}

open import Haskell.Prelude hiding (m;t)
open import Language.PlutusCore.Generators.NEAT.Common
open import Relation.Binary.PropositionalEquality

postulate Kind : Set → Set

-- * Enumeration

-- ** Enumerating types

data TypeBuiltinG : Set where
  TyByteStringG : TypeBuiltinG
  TyIntegerG    : TypeBuiltinG
  TyStringG     : TypeBuiltinG

{-# COMPILE AGDA2HS TypeBuiltinG deriving (Typeable, Eq, Show) #-}

{-# FOREIGN AGDA2HS
deriveEnumerable ''TypeBuiltinG
#-}

-- NOTE: Unusually, the application case is annotated with a kind.
--       The reason is eagerness and efficiency. If we have the kind
--       information at the application site, we can check the two
--       subterms in parallel, while evaluating as little as possible.

variable
  n m : Set

data TypeG (n : Set) : Set where
  TyVarG : n → TypeG n
  TyFunG : TypeG n → TypeG n → TypeG n
  TyIFixG : TypeG n  → Kind ⊤ → TypeG n → TypeG n
  TyForallG : Kind ⊤ → TypeG (S n) → TypeG n
  TyBuiltinG : TypeBuiltinG → TypeG n
  TyLamG : TypeG (S n) → TypeG n
  TyAppG : TypeG n → TypeG n → Kind ⊤ → TypeG n

{-# COMPILE AGDA2HS TypeG deriving (Typeable, Eq, Show) #-}
-- switched off deriving Functor

ext : (m → n) → S m → S n
ext f FZ     = FZ
ext f (FS x) = FS (f x)

{-# COMPILE AGDA2HS ext #-}

ren : (m → n) → TypeG m → TypeG n
ren f (TyVarG x) = TyVarG (f x)
ren f (TyFunG ty1 ty2) = TyFunG (ren f ty1) (ren f ty2)
ren f (TyIFixG ty1 k ty2) = TyIFixG (ren f ty1) k (ren f ty2)
ren f (TyForallG k ty) = TyForallG k (ren (ext f) ty)
ren f (TyBuiltinG b) = TyBuiltinG b
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

ext-id : (x : S m) → ext id x ≡ x
ext-id FZ     = refl
ext-id (FS x) = refl

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

{-# FOREIGN AGDA2HS
instance Functor TypeG where
  fmap = ren

newtype Neutral a = Neutral
  { unNeutral :: a
  }

deriveEnumerable ''Kind

deriveEnumerable ''TypeG

type ClosedTypeG = TypeG Z

{-

NOTE: We don't just want to enumerate arbitrary types but also normal
      types that cannot reduce any further. Neutral types are a subset
      of normal forms that consist of either a variable or a stuck
      application.

      Two approaches spring to mind:

      1. We could define a seperate AST for normal types and possibly
      also a seperate AST for terms with normalized types. This would
      be the safest option as it would then be impossible to generate
      a non-normalized type that claimed to be normalized. This is how
      it's done in the metatheory package. The downside is that there
      there is some duplication of code and/or it's a bit cumbersome and
      slow to convert from a normalized type back to an ordinary one.

     2. We could use a simple newtype wrapper to mark a type as
     normalized/neutral. This is how it's done in the plutus-core
     package. It's a helpful cue but there's nothing stopping us
     marking any type as normalised. This saves some extra work as we
     can conveniently unwrap a normal form and reuse code such as
     substitution.

     Here we go with option 2. The enumerable instances below explain
     how to construct a normalized or neutral type using the machinery of
     Control.Enumerable from the sized-based package.
-}

instance Enumerable tyname => Enumerable (Normalized (TypeG tyname)) where
  enumerate = share $ aconcat
    [       c1 $ \ty -> Normalized (unNeutral ty)
    , pay . c1 $ \ty -> Normalized (TyLamG (unNormalized ty))
    , pay . c3 $ \ty1 k ty2 -> Normalized (TyIFixG (unNormalized ty1) k (unNormalized ty2))
    , pay . c2 $ \k ty      -> Normalized (TyForallG k (unNormalized ty))
    , pay . c1 $ \tyBuiltin -> Normalized (TyBuiltinG tyBuiltin)
    , pay . c2 $ \ty1 ty2   -> Normalized (TyFunG (unNormalized ty1) (unNormalized ty2))
    ]

instance Enumerable tyname => Enumerable (Neutral (TypeG tyname)) where
  enumerate = share $ aconcat
    [ pay . c1 $ \i         -> Neutral (TyVarG i)
    , pay . c3 $ \ty1 ty2 k -> Neutral (TyAppG (unNeutral ty1) (unNormalized ty2) k)
    ]
#-}

-- * Normalisation

-- ** Type reduction

-- |Extend type substitutions.
extTySub : (n → TypeG m) -> S n → TypeG (S m)
extTySub _ FZ     = TyVarG FZ
extTySub s (FS i) = ren FS (s i) -- FS <$> s i

{-# COMPILE AGDA2HS extTySub #-}

-- |Simultaneous substitution of type variables.
applyTySub : (n -> TypeG m) -> TypeG n -> TypeG m
applyTySub s (TyVarG i)             = s i
applyTySub s (TyFunG ty1 ty2)       = TyFunG (applyTySub s ty1) (applyTySub s ty2)
applyTySub s (TyIFixG ty1 k ty2)    = TyIFixG (applyTySub s ty1) k (applyTySub s ty2)
applyTySub s (TyForallG k ty)       = TyForallG k (applyTySub (extTySub s) ty)
applyTySub _ (TyBuiltinG tyBuiltin) = TyBuiltinG tyBuiltin
applyTySub s (TyLamG ty)            = TyLamG (applyTySub (extTySub s) ty)
applyTySub s (TyAppG ty1 ty2 k)     = TyAppG (applyTySub s ty1) (applyTySub s ty2) k

{-# COMPILE AGDA2HS applyTySub #-}



{-# FOREIGN AGDA2HS
instance Monad TypeG where
  a >>= f = applyTySub f a
--  return = pure

instance Applicative TypeG where
  (<*>) = ap
  pure = TyVarG

-- |Reduce a generated type by a single step, or fail.
stepTypeG :: TypeG n -> Maybe (TypeG n)
stepTypeG (TyVarG _)                  = empty
stepTypeG (TyFunG ty1 ty2)            = (TyFunG <$> stepTypeG ty1 <*> pure ty2)
                                    <|> (TyFunG <$> pure ty1 <*> stepTypeG ty2)
stepTypeG (TyIFixG ty1 k ty2)         = (TyIFixG <$> stepTypeG ty1 <*> pure k <*> pure ty2)
                                    <|> (TyIFixG <$> pure ty1 <*> pure k <*> stepTypeG ty2)
stepTypeG (TyForallG k ty)            = TyForallG <$> pure k <*> stepTypeG ty
stepTypeG (TyBuiltinG _)              = empty
stepTypeG (TyLamG ty)                 = TyLamG <$> stepTypeG ty
stepTypeG (TyAppG (TyLamG ty1) ty2 _) = pure (applyTySub (\case FZ -> ty2; FS i -> TyVarG i) ty1)
stepTypeG (TyAppG ty1 ty2 k)          = (TyAppG <$> stepTypeG ty1 <*> pure ty2 <*> pure k)
                                    <|> (TyAppG <$> pure ty1 <*> stepTypeG ty2 <*> pure k)

-- |Normalise a generated type.
normalizeTypeG :: TypeG n -> TypeG n
normalizeTypeG ty = maybe ty normalizeTypeG (stepTypeG ty)

-- * Errors

-- NOTE: The errors we need to handle in property-based testing are
--       when the generator generates garbage (which shouldn't happen).
#-}
