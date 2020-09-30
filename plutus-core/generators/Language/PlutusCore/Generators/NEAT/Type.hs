{-|
Description: PLC Syntax, typechecker,semantics property based testing.

This file contains
1. A duplicate of the Plutus Core Abstract Syntax (types and terms)
2. A kind checker and a type checker
3. Reduction semantics for types
-}

{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE ExistentialQuantification #-}

module Language.PlutusCore.Generators.NEAT.Type
  ( TypeBuiltinG (..)
  , TypeG (..)
  , ClosedTypeG
  , toClosedType
  , checkClosedTypeG
  , normalizeTypeG
  , GenError (..)
  , ErrorP (..)
  ) where

import           Control.Enumerable
import           Control.Monad.Except
import           Data.Coolean
import qualified Data.Stream                                as Stream
import qualified Data.Text                                  as Text
import           Language.PlutusCore
import           Language.PlutusCore.DeBruijn
import           Language.PlutusCore.Generators.NEAT.Common

-- * Enumerating builtin types

data TypeBuiltinG
  = TyByteStringG
  | TyIntegerG
  | TyStringG
  deriving (Typeable, Eq, Show)

deriveEnumerable ''TypeBuiltinG

-- |Convert generated builtin types to Plutus builtin types.
toTypeBuiltin :: TypeBuiltinG -> Some (TypeIn DefaultUni)
toTypeBuiltin TyByteStringG = Some (TypeIn DefaultUniByteString)
toTypeBuiltin TyIntegerG    = Some (TypeIn DefaultUniInteger)
toTypeBuiltin TyStringG     = Some (TypeIn DefaultUniString)


-- * Enumerating types

-- NOTE: Unusually, the application case is annotated with a kind.
--       The reason is eagerness and efficiency. If we have the kind
--       information at the application site, we can check the two
--       subterms in parallel, while evaluating as little as possible.

data TypeG n
  = TyVarG n
  | TyFunG (TypeG n) (TypeG n)
  | TyIFixG (TypeG n) (Kind ()) (TypeG n)
  | TyForallG (Kind ()) (TypeG (S n))
  | TyBuiltinG TypeBuiltinG
  | TyLamG (TypeG (S n))
  | TyAppG (TypeG n) (TypeG n) (Kind ())
  deriving (Typeable, Eq, Show)

deriveEnumerable ''Kind

deriveEnumerable ''TypeG





-- NOTE: The errors we need to handle in property based testing are
--       when the generator generates garbage or we encounter an
--       actual type error in testing.

data GenError
 =  forall n. Show n => Gen (TypeG n) (Kind ())

data ErrorP ann
 = TypeErrorP (TypeError (Term TyName Name DefaultUni ()) DefaultUni ann)
 | AgdaErrorP ()
 | GenErrorP GenError
 | FVErrorP FreeVariableError


-- |Convert well-kinded generated types to Plutus types.
--
-- NOTE: Passes an explicit `TyNameState`, instead of using a State monad,
--       as the type of the `TyNameState` changes throughout the computation.
--       Alternatively, this could be written using an indexed State monad.
toType
  :: (Show n, MonadQuote m, MonadError GenError m)
  => TyNameState n      -- ^ Type name environment with fresh name stream
  -> Kind ()            -- ^ Kind of type below
  -> TypeG n            -- ^ Type to convert
  -> m (Type TyName DefaultUni ())
toType ns _ (TyVarG i) =
  return (TyVar () (tynameOf ns i))
toType ns (Type _) (TyFunG ty1 ty2) =
  TyFun () <$> toType ns (Type ()) ty1 <*> toType ns (Type ()) ty2
toType ns (Type _) (TyIFixG ty1 k ty2) =
  TyIFix () <$> toType ns k' ty1 <*> toType ns k ty2
  where
    k' = KindArrow () (KindArrow () k (Type ())) (KindArrow () k (Type ()))
toType ns (Type _) (TyForallG k ty) = do
  ns' <- extendTyNameState ns
  TyForall () (tynameOf ns' FZ) k <$> toType ns' (Type ()) ty
toType _ _ (TyBuiltinG tyBuiltin) =
  return (TyBuiltin () (toTypeBuiltin tyBuiltin))
toType ns (KindArrow _ k1 k2) (TyLamG ty) = do
  ns' <- extendTyNameState ns
  TyLam () (tynameOf ns' FZ) k1 <$> toType ns' k2 ty
toType ns k2 (TyAppG ty1 ty2 k1) =
  TyApp () <$> toType ns k' ty1 <*> toType ns k1 ty2
  where
    k' = KindArrow () k1 k2
toType _ k ty = throwError $ Gen ty k


-- * Enumerating closed types

type ClosedTypeG = TypeG Z


-- |Convert generated closed types to Plutus types.
toClosedType
  :: (MonadQuote m, MonadError GenError m)
  => Stream.Stream Text.Text
  -> Kind ()
  -> ClosedTypeG
  -> m (Type TyName DefaultUni ())
toClosedType strs = toType (emptyTyNameState strs)

-- * Kind checking

-- |Kind check builtin types.
--
-- NOTE: If we make |checkTypeBuiltinG| non-strict in its second argument,
--       lazy-search will only ever return one of the various builtin types.
--       Perhaps this is preferable?
--
checkTypeBuiltinG :: Kind () -> TypeBuiltinG -> Cool
checkTypeBuiltinG (Type _) TyByteStringG = true
checkTypeBuiltinG (Type _) TyIntegerG    = true
checkTypeBuiltinG (Type _) TyStringG     = true
checkTypeBuiltinG _        _             = false


-- |Kind check types.
checkTypeG :: KCS n -> Kind () -> TypeG n -> Cool
checkTypeG kcs k (TyVarG i)
  = varKindOk
  where
    varKindOk = toCool $ k == kindOf kcs i

checkTypeG kcs (Type _) (TyFunG ty1 ty2)
  = ty1KindOk &&& ty2KindOk
  where
    ty1KindOk = checkTypeG kcs (Type ()) ty1
    ty2KindOk = checkTypeG kcs (Type ()) ty2

checkTypeG kcs (Type _) (TyIFixG ty1 k ty2)
  = ty1KindOk &&& ty2KindOk
  where
    ty1Kind   =
      KindArrow () (KindArrow () k (Type ())) (KindArrow () k (Type ()))
    ty1KindOk = checkTypeG kcs ty1Kind ty1
    ty2KindOk = checkTypeG kcs k ty2

checkTypeG kcs (Type _) (TyForallG k body)
  = tyKindOk
  where
    tyKindOk = checkTypeG (extendKCS k kcs) (Type ()) body

checkTypeG _ k (TyBuiltinG tyBuiltin)
  = tyBuiltinKindOk
  where
    tyBuiltinKindOk = checkTypeBuiltinG k tyBuiltin

checkTypeG kcs (KindArrow () k1 k2) (TyLamG body)
  = bodyKindOk
  where
    bodyKindOk = checkTypeG (extendKCS k1 kcs) k2 body

checkTypeG kcs k' (TyAppG ty1 ty2 k)
  = ty1KindOk &&& ty2KindOk
  where
    ty1Kind   = KindArrow () k k'
    ty1KindOk = checkTypeG kcs ty1Kind ty1
    ty2KindOk = checkTypeG kcs k ty2

checkTypeG _ _ _ = false


-- |Kind check closed types.
checkClosedTypeG :: Kind () -> ClosedTypeG -> Cool
checkClosedTypeG = checkTypeG emptyKCS



-- * Kind checking state

newtype KCS n = KCS{ kindOf :: n -> Kind () }

emptyKCS :: KCS Z
emptyKCS = KCS{ kindOf = fromZ }

extendKCS :: forall n. Kind () -> KCS n -> KCS (S n)
extendKCS k KCS{..} = KCS{ kindOf = kindOf' }
  where
    kindOf' :: S n -> Kind ()
    kindOf' FZ     = k
    kindOf' (FS i) = kindOf i


-- * Normalising

-- |Extend renamings.
extendRen :: (n -> m) -> S n -> S m
extendRen _ FZ     = FZ
extendRen r (FS i) = FS (r i)

-- |Simultaneous renaming of variables in generated types.
renameTypeG :: (n -> m) -> TypeG n -> TypeG m
renameTypeG r (TyVarG i)             = TyVarG (r i)
renameTypeG r (TyFunG ty1 ty2)       = TyFunG (renameTypeG r ty1) (renameTypeG r ty2)
renameTypeG r (TyIFixG ty1 k ty2)    = TyIFixG (renameTypeG r ty1) k (renameTypeG r ty2)
renameTypeG r (TyForallG k ty)       = TyForallG k (renameTypeG (extendRen r) ty)
renameTypeG _ (TyBuiltinG tyBuiltin) = TyBuiltinG tyBuiltin
renameTypeG r (TyLamG ty)            = TyLamG (renameTypeG (extendRen r) ty)
renameTypeG r (TyAppG ty1 ty2 k)     = TyAppG (renameTypeG r ty1) (renameTypeG r ty2) k

-- |Extend substitutions.
extendSub :: (n -> TypeG m) -> S n -> TypeG (S m)
extendSub _ FZ     = TyVarG FZ
extendSub s (FS i) = renameTypeG FS (s i)

-- |Simultaneous substitution of variables in generated types.
substTypeG :: (n -> TypeG m) -> TypeG n -> TypeG m
substTypeG s (TyVarG i)             = s i
substTypeG s (TyFunG ty1 ty2)       = TyFunG (substTypeG s ty1) (substTypeG s ty2)
substTypeG s (TyIFixG ty1 k ty2)    = TyIFixG (substTypeG s ty1) k (substTypeG s ty2)
substTypeG s (TyForallG k ty)       = TyForallG k (substTypeG (extendSub s) ty)
substTypeG _ (TyBuiltinG tyBuiltin) = TyBuiltinG tyBuiltin
substTypeG s (TyLamG ty)            = TyLamG (substTypeG (extendSub s) ty)
substTypeG s (TyAppG ty1 ty2 k)     = TyAppG (substTypeG s ty1) (substTypeG s ty2) k

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
stepTypeG (TyAppG (TyLamG ty1) ty2 _) = pure (substTypeG (\case FZ -> ty2; FS i -> TyVarG i) ty1)
stepTypeG (TyAppG ty1 ty2 k)          = (TyAppG <$> stepTypeG ty1 <*> pure ty2 <*> pure k)
                                    <|> (TyAppG <$> pure ty1 <*> stepTypeG ty2 <*> pure k)

-- |Normalise a generated type.
normalizeTypeG :: TypeG n -> TypeG n
normalizeTypeG ty = maybe ty normalizeTypeG (stepTypeG ty)
