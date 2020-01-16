{-# LANGUAGE DeriveDataTypeable  #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}

module Language.PlutusCore.Type.Gen
  ( KindG (..)
  , TypeBuiltinG (..)
  , TypeG (..)
  , toClosedType
  , checkClosedTypeG
  ) where

import Language.PlutusCore (Type(..), TypeBuiltin(..), Kind(..))
import Control.Enumerable
import Data.Coolean
import Text.Printf



-- * Enumerating deBruijn indices

data Z
  deriving (Typeable, Eq, Show)

data S n
  = FZ
  | FS n
  deriving (Typeable, Eq, Show)

instance Enumerable Z where
  enumerate = datatype []

instance Enumerable n => Enumerable (S n) where
  enumerate = share $ aconcat
    [ c0 FZ
    , c1 FS
    ]

-- |Absurd for the zero type.
fromZ :: Z -> a
fromZ i = i `seq` error "instance of empty type Z"



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



-- * Enumerating builtin types

data TypeBuiltinG
  = TyByteStringG
  | TyIntegerG
  | TyStringG
  deriving (Typeable, Eq, Show)

$(deriveEnumerable ''TypeBuiltinG)

-- |Convert generated builtin types to Plutus builtin types.
toTypeBuiltin :: TypeBuiltinG -> TypeBuiltin
toTypeBuiltin TyByteStringG = TyByteString
toTypeBuiltin TyIntegerG    = TyInteger
toTypeBuiltin TyStringG     = TyString



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
toType :: Show n
       => NS tyname n -- ^ Namespace
       -> KindG       -- ^ Kind of the Type below
       -> TypeG n     -- ^ Type to convert
       -> Type tyname ()
toType ns _ (TyVarG i) = TyVar () (nameOf ns i)
toType ns TypeG (TyFunG ty1 ty2) = TyFun () (toType ns TypeG ty1) (toType ns TypeG ty2)
toType ns TypeG (TyIFixG ty1 k ty2) = TyIFix () (toType ns k' ty1) (toType ns TypeG ty2)
  where
    k' = (k `KindArrowG` TypeG) `KindArrowG` (k `KindArrowG` TypeG)
toType ns TypeG (TyForallG k ty) = TyForall () (nameOf ns' FZ) (toKind k) (toType ns' TypeG ty)
  where
    ns' = extendNS ns
toType _ _ (TyBuiltinG tyBuiltin) = TyBuiltin () (toTypeBuiltin tyBuiltin)
toType ns (KindArrowG k1 k2) (TyLamG ty) = TyLam () (nameOf ns' FZ) (toKind k1) (toType ns' k2 ty)
  where
    ns' = extendNS ns
toType ns k2 (TyAppG ty1 ty2 k1) = TyApp () (toType ns k' ty1) (toType ns k1 ty2)
  where
    k' = k1 `KindArrowG` k2
toType _ k ty = error (printf "toType: convert type %s at kind %s" (show ty) (show k))



-- * Enumerating closed types

type ClosedTypeG = TypeG Z


-- |Convert generated closed types to Plutus types.
toClosedType :: [tyname ()] -> KindG -> ClosedTypeG -> Type tyname ()
toClosedType fresh = toType NS{ nameOf = fromZ, fresh = fresh }



-- * Namespaces

data NS tyname n = NS { nameOf :: n -> tyname (), fresh :: [tyname ()] }


-- |Extend the type name map with a fresh name.
extendNS :: forall tyname n. NS tyname n -> NS tyname (S n)
extendNS NS{..} = NS{ nameOf = nameOf', fresh = tail fresh }
  where
    nameOf' :: S n -> tyname ()
    nameOf' FZ = head fresh
    nameOf' (FS i) = nameOf i



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
    ty2KindOk = checkTypeG kcs TypeG ty2

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
