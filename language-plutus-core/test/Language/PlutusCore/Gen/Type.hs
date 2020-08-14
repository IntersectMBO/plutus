{-|
Description: PLC Syntax, typechecker,semantics property based testing.

This file contains
1. A duplicate of the Plutus Core Abstract Syntax (types and terms)
2. A kind checker and a type checker
3. Reduction semantics for types
-}

{-# OPTIONS_GHC -fno-warn-orphans      #-}
{-# LANGUAGE DeriveDataTypeable        #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE RecordWildCards           #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE ExistentialQuantification #-}

module Language.PlutusCore.Gen.Type
  ( TypeBuiltinG (..)
  , TypeG (..)
  , ClosedTypeG
  , TermG (..)
  , ClosedTermG
  , toClosedType
  , checkClosedTypeG
  , normalizeTypeG
  , GenError (..)
  , ErrorP (..)
  ) where

import           Control.Enumerable
import           Control.Monad.Except
import           Data.Bifunctor
import           Data.Coolean
import qualified Data.Stream                    as Stream
import qualified Data.Text                      as Text
import           Language.PlutusCore
import           Language.PlutusCore.Gen.Common

-- * Enumeration

-- ** Enumerating types

data TypeBuiltinG
  = TyByteStringG
  | TyIntegerG
  | TyStringG
  deriving (Typeable, Eq, Show)

deriveEnumerable ''TypeBuiltinG

-- NOTE: Unusually, the application case is annotated with a kind.
--       The reason is eagerness and efficiency. If we have the kind
--       information at the application site, we can check the two
--       subterms in parallel, while evaluating as little as possible.

data TypeG tyname
  = TyVarG tyname
  | TyFunG (TypeG tyname) (TypeG tyname)
  | TyIFixG (TypeG tyname) (Kind ()) (TypeG tyname)
  | TyForallG (Kind ()) (TypeG (S tyname))
  | TyBuiltinG TypeBuiltinG
  | TyLamG (TypeG (S tyname))
  | TyAppG (TypeG tyname) (TypeG tyname) (Kind ())
  deriving (Typeable, Eq, Show, Functor)

deriveEnumerable ''Kind

deriveEnumerable ''TypeG

type ClosedTypeG = TypeG Z


-- ** Enumerating terms

-- NOTE: We're not generating constants, dynamic builtins, or errors.

data TermG tyname name
    = VarG name
    | TyAbsG (TermG (S tyname) name)
    | LamAbsG (TermG tyname (S name))
    | ApplyG (TermG tyname name) (TermG tyname name) (TypeG tyname)
    | BuiltinG StaticBuiltinName
    | TyInstG (TermG tyname name) (TypeG tyname) (Kind ())
    | UnwrapG (TermG tyname name)
    | IWrapG (TypeG tyname) (TypeG tyname) (TermG tyname name)
    deriving (Typeable, Eq, Show)

instance Bifunctor TermG where
  bimap _ g (VarG i)            = VarG (g i)
  bimap f g (TyAbsG tm)         = TyAbsG (bimap (fmap f) g tm)
  bimap f g (LamAbsG tm)        = LamAbsG (bimap f (fmap g) tm)
  bimap f g (ApplyG tm1 tm2 ty) = ApplyG (bimap f g tm1) (bimap f g tm2) (fmap f ty)
  bimap _ _ (BuiltinG builtin)  = BuiltinG builtin
  bimap f g (TyInstG tm ty k)   = TyInstG (bimap f g tm) (fmap f ty) k
  bimap f g (UnwrapG tm)        = UnwrapG (bimap f g tm)
  bimap f g (IWrapG ty1 ty2 tm) = IWrapG (fmap f ty1) (fmap f ty2) (bimap f g tm)

deriveEnumerable ''StaticBuiltinName

deriveEnumerable ''TermG

type ClosedTermG = TermG Z Z


-- * Conversion to PlutusCore

-- NOTE: The errors we need to handle in property based testing are
--       when the generator generates garbage or we encounter an
--       actual type error in testing.

data GenError
 =  forall n. Show n => Gen (TypeG n) (Kind ())

data ErrorP ann
 = TypeErrorP (TypeError DefaultUni ann)
 | GenErrorP GenError


-- * Converting types

-- |Convert generated builtin types to Plutus builtin types.
toTypeBuiltin :: TypeBuiltinG -> Some (TypeIn DefaultUni)
toTypeBuiltin TyByteStringG = Some (TypeIn DefaultUniByteString)
toTypeBuiltin TyIntegerG    = Some (TypeIn DefaultUniInteger)
toTypeBuiltin TyStringG     = Some (TypeIn DefaultUniString)


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


-- |Convert generated closed types to Plutus types.
toClosedType
  :: (MonadQuote m, MonadError GenError m)
  => Stream.Stream Text.Text
  -> Kind ()
  -> ClosedTypeG
  -> m (Type TyName DefaultUni ())
toClosedType strs = toType (emptyTyNameState strs)

-- ** Converting terms


-- * Checking

-- ** Kind checking

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


-- ** Kind checking state

newtype KCS n = KCS{ kindOf :: n -> Kind () }

emptyKCS :: KCS Z
emptyKCS = KCS{ kindOf = fromZ }

extendKCS :: forall n. Kind () -> KCS n -> KCS (S n)
extendKCS k KCS{..} = KCS{ kindOf = kindOf' }
  where
    kindOf' :: S n -> Kind ()
    kindOf' FZ     = k
    kindOf' (FS i) = kindOf i


-- * Normalisation

-- ** Type reduction

type TySub n m = n -> TypeG m

-- |Extend substitutions.
extTySub :: TySub n m -> TySub (S n) (S m)
extTySub _ FZ     = TyVarG FZ
extTySub s (FS i) = FS <$> s i

-- |Simultaneous substitution of variables in generated types.
applyTySub :: (n -> TypeG m) -> TypeG n -> TypeG m
applyTySub s (TyVarG i)             = s i
applyTySub s (TyFunG ty1 ty2)       = TyFunG (applyTySub s ty1) (applyTySub s ty2)
applyTySub s (TyIFixG ty1 k ty2)    = TyIFixG (applyTySub s ty1) k (applyTySub s ty2)
applyTySub s (TyForallG k ty)       = TyForallG k (applyTySub (extTySub s) ty)
applyTySub _ (TyBuiltinG tyBuiltin) = TyBuiltinG tyBuiltin
applyTySub s (TyLamG ty)            = TyLamG (applyTySub (extTySub s) ty)
applyTySub s (TyAppG ty1 ty2 k)     = TyAppG (applyTySub s ty1) (applyTySub s ty2) k

-- |Reduce a generated type by a single step, or fail.
stepTy :: TypeG n -> Maybe (TypeG n)
stepTy (TyVarG _)                  = empty
stepTy (TyFunG ty1 ty2)            = (TyFunG <$> stepTy ty1 <*> pure ty2)
                                    <|> (TyFunG <$> pure ty1 <*> stepTy ty2)
stepTy (TyIFixG ty1 k ty2)         = (TyIFixG <$> stepTy ty1 <*> pure k <*> pure ty2)
                                    <|> (TyIFixG <$> pure ty1 <*> pure k <*> stepTy ty2)
stepTy (TyForallG k ty)            = TyForallG <$> pure k <*> stepTy ty
stepTy (TyBuiltinG _)              = empty
stepTy (TyLamG ty)                 = TyLamG <$> stepTy ty
stepTy (TyAppG (TyLamG ty1) ty2 _) = pure (applyTySub (\case FZ -> ty2; FS i -> TyVarG i) ty1)
stepTy (TyAppG ty1 ty2 k)          = TyAppG <$> stepTy ty1 <*> pure ty2 <*> pure k

-- |Normalise a generated type.
normalizeTypeG :: TypeG n -> TypeG n
normalizeTypeG ty = maybe ty normalizeTypeG (stepTy ty)
