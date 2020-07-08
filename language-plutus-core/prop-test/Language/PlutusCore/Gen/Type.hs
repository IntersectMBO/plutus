{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}

module Language.PlutusCore.Gen.Type
  ( KindG (..)
  , TypeBuiltinG (..)
  , TypeG (..)
  , ClosedTypeG
  , toClosedType
  , checkClosedTypeG
  , toKind
  , fromKind
  , normalizeTypeG
  ) where

import           Language.PlutusCore
import           Language.PlutusCore.Gen.Common
import           Control.Enumerable
import           Data.Coolean
import qualified Data.Text as Text
import           Text.Printf


-- * Enumerating kinds

data KindG
  = TypeG
  | KindArrowG KindG KindG
  deriving (Typeable, Eq, Show)

$(deriveEnumerable ''KindG)


-- |Convert generated kinds to Plutus kinds.
toKind :: KindG -> Kind ()
toKind TypeG              = Type ()
toKind (KindArrowG k1 k2) = KindArrow () (toKind k1) (toKind k2)


-- |Convert Plutus kinds to generated kinds.
fromKind :: Kind ann -> KindG
fromKind (Type _)            = TypeG
fromKind (KindArrow _ k1 k2) = KindArrowG (fromKind k1) (fromKind k2)


-- * Enumerating builtin types

data TypeBuiltinG
  = TyByteStringG
  | TyIntegerG
  | TyStringG
  deriving (Typeable, Eq, Show)

$(deriveEnumerable ''TypeBuiltinG)

-- |Convert generated builtin types to Plutus builtin types.
{-
toTypeBuiltin :: TypeBuiltinG -> TypeBuiltin
toTypeBuiltin TyByteStringG = TyByteString
toTypeBuiltin TyIntegerG    = TyInteger
toTypeBuiltin TyStringG     = TyString
-}
toTypeBuiltin :: TypeBuiltinG -> Some (TypeIn DefaultUni)
toTypeBuiltin TyByteStringG = Some (TypeIn DefaultUniByteString)
toTypeBuiltin TyIntegerG    = Some (TypeIn DefaultUniInteger)
toTypeBuiltin TyStringG     = Some (TypeIn DefaultUniString)


-- * Enumerating types

data TypeG n
  = TyVarG n
  | TyFunG (TypeG n) (TypeG n)
  | TyIFixG (TypeG n) KindG (TypeG n)
  | TyForallG KindG (TypeG (S n))
  | TyBuiltinG TypeBuiltinG
  | TyLamG (TypeG (S n))
  | TyAppG (TypeG n) (TypeG n) KindG
  deriving (Typeable, Eq, Show)

$(deriveEnumerable ''TypeG)


-- |Convert well-kinded generated types to Plutus types.
--
-- NOTE: Passes an explicit `TyNameState`, instead of using a State monad,
--       as the type of the `TyNameState` changes throughout the computation.
--       Alternatively, this could be written using an indexed State monad.
--
-- NOTE: The error types in Language.PlutusCore.Error are closed, and hence it
--       isn't possible to define new possible errors without introducing them
--       for the full language. Since conversion errors always indicate an
--       internal error in `checkKindG`, I'm deciding to just use `error`.
toType
  :: (Show n, MonadQuote m)
  => TyNameState n      -- ^ Type name environment with fresh name stream
  -> KindG              -- ^ Kind of type below
  -> TypeG n            -- ^ Type to convert
  -> m (Type TyName DefaultUni ())
toType ns _ (TyVarG i) =
  return (TyVar () (tynameOf ns i))
toType ns TypeG (TyFunG ty1 ty2) =
  TyFun () <$> toType ns TypeG ty1 <*> toType ns TypeG ty2
toType ns TypeG (TyIFixG ty1 k ty2) =
  TyIFix () <$> toType ns k' ty1 <*> toType ns k ty2
  where
    k' = (k `KindArrowG` TypeG) `KindArrowG` (k `KindArrowG` TypeG)
toType ns TypeG (TyForallG k ty) = do
  ns' <- extendTyNameState ns
  TyForall () (tynameOf ns' FZ) (toKind k) <$> toType ns' TypeG ty
toType _ _ (TyBuiltinG tyBuiltin) =
  return (TyBuiltin () (toTypeBuiltin tyBuiltin))
toType ns (KindArrowG k1 k2) (TyLamG ty) = do
  ns' <- extendTyNameState ns
  TyLam () (tynameOf ns' FZ) (toKind k1) <$> toType ns' k2 ty
toType ns k2 (TyAppG ty1 ty2 k1) =
  TyApp () <$> toType ns k' ty1 <*> toType ns k1 ty2
  where
    k' = k1 `KindArrowG` k2
toType _ k ty =
  error (printf "toType: convert type %s at kind %s" (show ty) (show k))



-- * Enumerating closed types

type ClosedTypeG = TypeG Z


-- |Convert generated closed types to Plutus types.
toClosedType
  :: (MonadQuote m)
  => [Text.Text]
  -> KindG
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
checkTypeBuiltinG :: KindG -> TypeBuiltinG -> Cool
checkTypeBuiltinG TypeG TyByteStringG = true
checkTypeBuiltinG TypeG TyIntegerG    = true
checkTypeBuiltinG TypeG TyStringG     = true
checkTypeBuiltinG _     _             = false


-- |Kind check types.
checkTypeG :: KCS n -> KindG -> TypeG n -> Cool
checkTypeG kcs k (TyVarG i)
  = varKindOk
  where
    varKindOk = toCool $ k == kindOf kcs i

checkTypeG kcs TypeG (TyFunG ty1 ty2)
  = ty1KindOk &&& ty2KindOk
  where
    ty1KindOk = checkTypeG kcs TypeG ty1
    ty2KindOk = checkTypeG kcs TypeG ty2

checkTypeG kcs TypeG (TyIFixG ty1 k ty2)
  = ty1KindOk &&& ty2KindOk
  where
    ty1Kind   = (k `KindArrowG` TypeG) `KindArrowG` (k `KindArrowG` TypeG)
    ty1KindOk = checkTypeG kcs ty1Kind ty1
    ty2KindOk = checkTypeG kcs k ty2

checkTypeG kcs TypeG (TyForallG k body)
  = tyKindOk
  where
    tyKindOk = checkTypeG (extendKCS k kcs) TypeG body

checkTypeG _ k (TyBuiltinG tyBuiltin)
  = tyBuiltinKindOk
  where
    tyBuiltinKindOk = checkTypeBuiltinG k tyBuiltin

checkTypeG kcs (k1 `KindArrowG` k2) (TyLamG body)
  = bodyKindOk
  where
    bodyKindOk = checkTypeG (extendKCS k1 kcs) k2 body

checkTypeG kcs k' (TyAppG ty1 ty2 k)
  = ty1KindOk &&& ty2KindOk
  where
    ty1Kind   = k `KindArrowG` k'
    ty1KindOk = checkTypeG kcs ty1Kind ty1
    ty2KindOk = checkTypeG kcs k ty2

checkTypeG _ _ _ = false


-- |Kind check closed types.
checkClosedTypeG :: KindG -> ClosedTypeG -> Cool
checkClosedTypeG = checkTypeG emptyKCS



-- * Kind checking state

newtype KCS n = KCS{ kindOf :: n -> KindG }

emptyKCS :: KCS Z
emptyKCS = KCS{ kindOf = fromZ }

extendKCS :: forall n. KindG -> KCS n -> KCS (S n)
extendKCS k KCS{..} = KCS{ kindOf = kindOf' }
  where
    kindOf' :: S n -> KindG
    kindOf' FZ = k
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
