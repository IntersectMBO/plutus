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

module Language.PlutusCore.Generators.NEAT.Type where















import           Control.Enumerable
import           Control.Monad.Except
import           Language.PlutusCore
import           Language.PlutusCore.Generators.NEAT.Common

data TypeBuiltinG = TyByteStringG
                  | TyIntegerG
                  | TyStringG
                      deriving (Typeable, Eq, Show)

deriveEnumerable ''TypeBuiltinG

data TypeG n = TyVarG n
             | TyFunG (TypeG n) (TypeG n)
             | TyIFixG (TypeG n) (Kind ()) (TypeG n)
             | TyForallG (Kind ()) (TypeG (S n))
             | TyBuiltinG TypeBuiltinG
             | TyLamG (TypeG (S n))
             | TyAppG (TypeG n) (TypeG n) (Kind ())
                 deriving (Typeable, Eq, Show)

ext :: (m -> n) -> S m -> S n
ext _ FZ     = FZ
ext f (FS x) = FS (f x)

ren :: (m -> n) -> TypeG m -> TypeG n
ren f (TyVarG x)          = TyVarG (f x)
ren f (TyFunG ty1 ty2)    = TyFunG (ren f ty1) (ren f ty2)
ren f (TyIFixG ty1 k ty2) = TyIFixG (ren f ty1) k (ren f ty2)
ren f (TyForallG k ty)    = TyForallG k (ren (ext f) ty)
ren _ (TyBuiltinG b)      = TyBuiltinG b
ren f (TyLamG ty)         = TyLamG (ren (ext f) ty)
ren f (TyAppG ty1 ty2 k)  = TyAppG (ren f ty1) (ren f ty2) k

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

extTySub :: (n -> TypeG m) -> S n -> TypeG (S m)
extTySub _ FZ     = TyVarG FZ
extTySub s (FS i) = ren FS (s i)

applyTySub :: (n -> TypeG m) -> TypeG n -> TypeG m
applyTySub s (TyVarG i) = s i
applyTySub s (TyFunG ty1 ty2)
  = TyFunG (applyTySub s ty1) (applyTySub s ty2)
applyTySub s (TyIFixG ty1 k ty2)
  = TyIFixG (applyTySub s ty1) k (applyTySub s ty2)
applyTySub s (TyForallG k ty)
  = TyForallG k (applyTySub (extTySub s) ty)
applyTySub _ (TyBuiltinG tyBuiltin) = TyBuiltinG tyBuiltin
applyTySub s (TyLamG ty) = TyLamG (applyTySub (extTySub s) ty)
applyTySub s (TyAppG ty1 ty2 k)
  = TyAppG (applyTySub s ty1) (applyTySub s ty2) k

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

