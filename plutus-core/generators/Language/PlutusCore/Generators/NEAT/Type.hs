{-| Description: PLC Syntax, typechecker,semantics property based testing.

This file contains
1. A duplicate of the Plutus Core Abstract Syntax (types and terms)
2. A kind checker and a type checker
3. Reduction semantics for types
-}

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

module Language.PlutusCore.Generators.NEAT.Type
  ( TypeBuiltinG (..)
  , TypeG (..)
  , ClosedTypeG
  , convertClosedType
  , TermG (..)
  , ClosedTermG
  , convertClosedTerm
  , Check (..)
  , stepTypeG
  , normalizeTypeG
  , GenError (..)
  , Neutral (..)
  ) where

import           Control.Enumerable
import           Control.Monad.Except
import           Data.Bifunctor.TH
import           Data.Coolean                               (Cool, false, toCool, true, (&&&))
import qualified Data.Stream                                as Stream
import qualified Data.Text                                  as Text
import           Language.PlutusCore
import           Language.PlutusCore.Generators.NEAT.Common
import           Text.Printf

newtype Neutral a = Neutral
  { unNeutral :: a
  }


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

-- ** Enumerating terms

data TermG tyname name
    = VarG
      name
    | LamAbsG
      (TermG tyname (S name))
    | ApplyG
      (TermG tyname name)
      (TermG tyname name)
      (TypeG tyname)
    | TyAbsG
      (TermG (S tyname) name)
    | TyInstG
      (TermG tyname name)
      (TypeG (S tyname))
      (TypeG tyname)
      (Kind ())
    deriving (Typeable, Eq, Show)

deriveBifunctor ''TermG
deriveEnumerable ''StaticBuiltinName
deriveEnumerable ''TermG

type ClosedTermG = TermG Z Z


-- * Converting types

-- |Convert generated builtin types to Plutus builtin types.
convertTypeBuiltin :: TypeBuiltinG -> Some (TypeIn DefaultUni)
convertTypeBuiltin TyByteStringG = Some (TypeIn DefaultUniByteString)
convertTypeBuiltin TyIntegerG    = Some (TypeIn DefaultUniInteger)
convertTypeBuiltin TyStringG     = Some (TypeIn DefaultUniString)

-- |Convert well-kinded generated types to Plutus types.
--
-- NOTE: Passes an explicit `TyNameState`, instead of using a State
--       monad, as the type of the `TyNameState` changes throughout
--       the computation.  Alternatively, this could be written using
--       an indexed State monad.
--
-- NOTE: Roman points out that this is more like reader than state,
--       however it doesn't fit easily into this pattern as the
--       function `extTyNameState` is monadic (`MonadQuote`).
convertType
  :: (Show tyname, MonadQuote m, MonadError GenError m)
  => TyNameState tyname -- ^ Type name environment with fresh name stream
  -> Kind ()            -- ^ Kind of type below
  -> TypeG tyname       -- ^ Type to convert
  -> m (Type TyName DefaultUni ())
convertType tns _ (TyVarG i) =
  return (TyVar () (tynameOf tns i))
convertType tns (Type _) (TyFunG ty1 ty2) =
  TyFun () <$> convertType tns (Type ()) ty1 <*> convertType tns (Type ()) ty2
convertType tns (Type _) (TyIFixG ty1 k ty2) =
  TyIFix () <$> convertType tns k' ty1 <*> convertType tns k ty2
  where
    k' = KindArrow () (KindArrow () k (Type ())) (KindArrow () k (Type ()))
convertType tns (Type _) (TyForallG k ty) = do
  tns' <- extTyNameState tns
  TyForall () (tynameOf tns' FZ) k <$> convertType tns' (Type ()) ty
convertType _ _ (TyBuiltinG tyBuiltin) =
  return (TyBuiltin () (convertTypeBuiltin tyBuiltin))
convertType tns (KindArrow _ k1 k2) (TyLamG ty) = do
  tns' <- extTyNameState tns
  TyLam () (tynameOf tns' FZ) k1 <$> convertType tns' k2 ty
convertType tns k2 (TyAppG ty1 ty2 k1) =
  TyApp () <$> convertType tns (KindArrow () k1 k2) ty1 <*> convertType tns k1 ty2
convertType _ k ty = throwError $ BadTypeG k ty

-- |Convert generated closed types to Plutus types.
convertClosedType
  :: (MonadQuote m, MonadError GenError m)
  => Stream.Stream Text.Text
  -> Kind ()
  -> ClosedTypeG
  -> m (Type TyName DefaultUni ())
convertClosedType tynames = convertType (emptyTyNameState tynames)


-- ** Converting terms

-- |Convert (well-typed) generated terms to Plutus terms.
--
-- NOTE: Passes an explicit `TyNameState` and `NameState`, instead of using a
--       State monad, as the type of the `TyNameState` changes throughout the
--       computation. This could be written using an indexed State monad.
--
--       No checking is performed during conversion. The type is given
--       as it contains information needed to fully annotate a `Term`.
--       `Term`, unlike `TermG`, contains all necessary type
--       information to infer the type of the term. It is expected
--       that this function is only called on a well-typed
--       term. Violating this would point to an error in the
--       generator/checker.
convertTerm
  :: (Show tyname, Show name, MonadQuote m, MonadError GenError m)
  => TyNameState tyname -- ^ Type name environment with fresh name stream
  -> NameState name     -- ^ Name environment with fresh name stream
  -> TypeG tyname       -- ^ Type of term below
  -> TermG tyname name  -- ^ Term to convert
  -> m (Term TyName Name DefaultUni ())
convertTerm _tns ns _ty (VarG i) =
  return (Var () (nameOf ns i))
convertTerm tns ns (TyFunG ty1 ty2) (LamAbsG tm) = do
  ns' <- extNameState ns
  ty1' <- convertType tns (Type ()) ty1
  LamAbs () (nameOf ns' FZ) ty1' <$> convertTerm tns ns' ty2 tm
convertTerm tns ns ty2 (ApplyG tm1 tm2 ty1) =
  Apply () <$> convertTerm tns ns (TyFunG ty1 ty2) tm1 <*> convertTerm tns ns ty1 tm2
convertTerm tns ns (TyForallG k ty) (TyAbsG tm) = do
  tns' <- extTyNameState tns
  TyAbs () (tynameOf tns' FZ) k <$> convertTerm tns' ns ty tm
convertTerm tns ns _ (TyInstG tm cod ty k) =
  TyInst () <$> convertTerm tns ns (TyForallG k cod) tm <*> convertType tns k ty
convertTerm _ _ ty tm = throwError $ BadTermG ty tm

-- |Convert generated closed terms to Plutus terms.
convertClosedTerm
  :: (MonadQuote m, MonadError GenError m)
  => Stream.Stream Text.Text
  -> Stream.Stream Text.Text
  -> ClosedTypeG
  -> ClosedTermG
  -> m (Term TyName Name DefaultUni ())
convertClosedTerm tynames names = convertTerm (emptyTyNameState tynames) (emptyNameState names)


-- * Checking

class Check t a where
  check :: t -> a -> Cool


-- ** Kind checking

-- |Kind check builtin types.
--
-- NOTE: If we make |checkTypeBuiltinG| non-strict in its second argument,
--       lazy-search will only ever return one of the various builtin types.
--       Perhaps this is preferable?
--
instance Check (Kind ()) TypeBuiltinG where
  check (Type _) TyByteStringG = true
  check (Type _) TyIntegerG    = true
  check (Type _) TyStringG     = true
  check _        _             = false


-- |Kind check types.
checkKindG :: KCS n -> Kind () -> TypeG n -> Cool
checkKindG kcs k (TyVarG i)
  = varKindOk
  where
    varKindOk = toCool $ k == kindOf kcs i

checkKindG kcs (Type _) (TyFunG ty1 ty2)
  = ty1KindOk &&& ty2KindOk
  where
    ty1KindOk = checkKindG kcs (Type ()) ty1
    ty2KindOk = checkKindG kcs (Type ()) ty2

checkKindG kcs (Type _) (TyIFixG ty1 k ty2)
  = ty1KindOk &&& ty2KindOk
  where
    ty1Kind   =
      KindArrow () (KindArrow () k (Type ())) (KindArrow () k (Type ()))
    ty1KindOk = checkKindG kcs ty1Kind ty1
    ty2KindOk = checkKindG kcs k ty2

checkKindG kcs (Type _) (TyForallG k body)
  = tyKindOk
  where
    tyKindOk = checkKindG (extKCS k kcs) (Type ()) body

checkKindG _ k (TyBuiltinG tyBuiltin)
  = tyBuiltinKindOk
  where
    tyBuiltinKindOk = check k tyBuiltin

checkKindG kcs (KindArrow () k1 k2) (TyLamG body)
  = bodyKindOk
  where
    bodyKindOk = checkKindG (extKCS k1 kcs) k2 body

checkKindG kcs k' (TyAppG ty1 ty2 k)
  = ty1KindOk &&& ty2KindOk
  where
    ty1Kind   = KindArrow () k k'
    ty1KindOk = checkKindG kcs ty1Kind ty1
    ty2KindOk = checkKindG kcs k ty2

checkKindG _ _ _ = false


instance Check (Kind ()) ClosedTypeG where
  check = checkKindG emptyKCS


instance Check (Kind ()) (Normalized ClosedTypeG) where
  check k ty = check k (unNormalized ty)


-- ** Kind checking state

newtype KCS tyname = KCS{ kindOf :: tyname -> Kind () }

emptyKCS :: KCS Z
emptyKCS = KCS{ kindOf = fromZ }

extKCS :: forall tyname. Kind () -> KCS tyname -> KCS (S tyname)
extKCS k KCS{..} = KCS{ kindOf = kindOf' }
  where
    kindOf' :: S tyname -> Kind ()
    kindOf' FZ     = k
    kindOf' (FS i) = kindOf i


-- ** Type checking

checkTypeG
  :: Eq tyname
  => KCS tyname
  -> TCS tyname name
  -> TypeG tyname
  -> TermG tyname name
  -> Cool
checkTypeG _ tcs ty (VarG i)
  = varTypeOk
  where
    varTypeOk = toCool $ ty == typeOf tcs i

checkTypeG kcs tcs (TyForallG k ty) (TyAbsG tm)
  = tmTypeOk
  where
    tmTypeOk = checkTypeG (extKCS k kcs) (firstTCS FS tcs) ty tm

checkTypeG kcs tcs (TyFunG ty1 ty2) (LamAbsG tm)
  = tyKindOk &&& tmTypeOk
  where
    tyKindOk = checkKindG kcs (Type ()) ty1
    tmTypeOk = checkTypeG kcs (extTCS ty1 tcs) ty2 tm

checkTypeG kcs tcs ty2 (ApplyG tm1 tm2 ty1)
  = tm1TypeOk &&& tm2TypeOk
  where
    tm1TypeOk = checkTypeG kcs tcs (TyFunG ty1 ty2) tm1
    tm2TypeOk = checkTypeG kcs tcs ty1 tm2

checkTypeG kcs tcs vTy (TyInstG tm vCod ty k)
  = tmTypeOk &&& tyKindOk &&& tyOk
  where
    tmTypeOk = checkTypeG kcs tcs (TyForallG k vCod) tm
    tyKindOk = checkKindG kcs k ty
    tyOk = vTy == normalizeTypeG (TyAppG (TyLamG vCod) ty k)

checkTypeG _ _ _ _ = false

instance Check ClosedTypeG ClosedTermG where
  check = checkTypeG emptyKCS emptyTCS


-- ** Type checking state

newtype TCS tyname name = TCS{ typeOf :: name -> TypeG tyname }

emptyTCS :: TCS tyname Z
emptyTCS = TCS{ typeOf = fromZ }

extTCS :: forall tyname name. TypeG tyname -> TCS tyname name -> TCS tyname (S name)
extTCS ty TCS{..} = TCS{ typeOf = typeOf' }
  where
    typeOf' :: S name -> TypeG tyname
    typeOf' FZ     = ty
    typeOf' (FS i) = typeOf i

firstTCS :: (tyname -> tyname') -> TCS tyname name -> TCS tyname' name
firstTCS f tcs = TCS{ typeOf = fmap f . typeOf tcs }


-- * Normalisation

-- ** Type reduction

type TySub n m = n -> TypeG m

-- |Extend type substitutions.
extTySub :: TySub n m -> TySub (S n) (S m)
extTySub _ FZ     = TyVarG FZ
extTySub s (FS i) = FS <$> s i


-- |Simultaneous substitution of type variables.
applyTySub :: (n -> TypeG m) -> TypeG n -> TypeG m
applyTySub s (TyVarG i)             = s i
applyTySub s (TyFunG ty1 ty2)       = TyFunG (applyTySub s ty1) (applyTySub s ty2)
applyTySub s (TyIFixG ty1 k ty2)    = TyIFixG (applyTySub s ty1) k (applyTySub s ty2)
applyTySub s (TyForallG k ty)       = TyForallG k (applyTySub (extTySub s) ty)
applyTySub _ (TyBuiltinG tyBuiltin) = TyBuiltinG tyBuiltin
applyTySub s (TyLamG ty)            = TyLamG (applyTySub (extTySub s) ty)
applyTySub s (TyAppG ty1 ty2 k)     = TyAppG (applyTySub s ty1) (applyTySub s ty2) k

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

data GenError
  = forall tyname. Show tyname => BadTypeG (Kind ()) (TypeG tyname)
  | forall tyname name. (Show tyname, Show name) => BadTermG (TypeG tyname) (TermG tyname name)

instance Show GenError where
  show (BadTypeG k ty) =
    printf "Test generation error: convert type %s at kind %s" (show ty) (show k)
  show (BadTermG ty tm) =
    printf "Test generation error: convert term %s at type %s" (show tm) (show ty)
