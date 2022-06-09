{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveAnyClass        #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DerivingVia           #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE ImportQualifiedPost   #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NumericUnderscores    #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TupleSections         #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module PlutusCore.Generators.PIR.Utils where

import Prettyprinter

import Control.Monad.Reader

import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.String
import Test.QuickCheck

import PlutusCore.Default
import PlutusCore.Generators.PIR.Common
import PlutusCore.Name
import PlutusIR
import PlutusIR.Subst

import PlutusCore.Generators.PIR.GenTm
import PlutusIR.Core.Instance.Pretty.Readable

-- | Show a `Doc` when a property fails.
ceDoc :: Testable t => Doc ann -> t -> Property
ceDoc d = counterexample (show d)

-- | Bind a value to a name in a property so that
-- it is displayed as a `name = thing` binding if the
-- property fails.
letCE :: (PrettyPir a, Testable p)
      => String
      -> a
      -> (a -> p)
      -> Property
letCE name x k = ceDoc (fromString name <+> "=" <+> prettyPirReadable x) (k x)

-- | Like `forAllShrink` but displays the bound value as
-- a named pretty-printed binding like `letCE`
forAllDoc :: (PrettyPir a, Testable p)
          => String
          -> Gen a
          -> (a -> [a])
          -> (a -> p)
          -> Property
forAllDoc name g shr k =
  forAllShrinkBlind g shr $ \ x ->
    ceDoc (fromString name <+> "=" <+> prettyPirReadable x)
          (k x)

-- | Check that a list of potential counterexamples is empty and display the
-- list as a QuickCheck counterexample if its not.
assertNoCounterexamples :: PrettyPir a => [a] -> Property
assertNoCounterexamples []  = property True
assertNoCounterexamples bad = ceDoc (prettyPirReadable bad) False

-- * Dealing with fresh names

-- | Get the free type variables in a type along with how many
-- times they occur. The elements of the map are guaranteed to be
-- non-zero.
fvTypeBag :: Type TyName DefaultUni () -> Map TyName Int
fvTypeBag ty = case ty of
  TyVar _ x        -> Map.singleton x 1
  TyFun _ a b      -> Map.unionWith (+) (fvTypeBag a) (fvTypeBag b)
  TyApp _ a b      -> Map.unionWith (+) (fvTypeBag a) (fvTypeBag b)
  TyLam _ x _ b    -> Map.delete x (fvTypeBag b)
  TyForall _ x _ b -> Map.delete x (fvTypeBag b)
  TyBuiltin{}      -> Map.empty
  TyIFix{}         -> error "fvTypeBag: TyIFix"

-- | Get the free variables in a type that appear in negative position
-- Note: This is used to ensure we only generate positive datatypes.
negativeVars :: Type TyName DefaultUni () -> Set TyName
negativeVars ty = case ty of
  TyFun _ a b      -> positiveVars a <> negativeVars b
  TyApp _ a b      -> negativeVars a <> negativeVars b
  TyLam _ x _ b    -> Set.delete x $ negativeVars b
  TyForall _ x _ b -> Set.delete x $ negativeVars b
  TyVar _ _        -> mempty
  TyBuiltin{}      -> mempty
  TyIFix{}         -> error "negativeVars: TyIFix"

-- | Get the free variables in a type that appear in positive position
positiveVars :: Type TyName DefaultUni () -> Set TyName
positiveVars ty = case ty of
  TyFun _ a b      -> negativeVars a <> positiveVars b
  TyApp _ a b      -> positiveVars a <> positiveVars b
  TyLam _ x _ b    -> Set.delete x $ positiveVars b
  TyForall _ x _ b -> Set.delete x $ positiveVars b
  TyVar _ x        -> Set.singleton x
  TyBuiltin{}      -> mempty
  TyIFix{}         -> error "positiveVars: TyIFix"

-- | Freshen a TyName so that it does not equal any of the names in the set.
freshenTyName :: Set TyName -> TyName -> TyName
freshenTyName fvs (TyName (Name x j)) = TyName (Name x i)
  where i  = succ $ Set.findMax is
        is = Set.insert j $ Set.insert (toEnum 0) $ Set.mapMonotonic (nameUnique . unTyName) fvs

-- | Get the names and types of the constructors of a datatype.
constrTypes :: Datatype TyName Name DefaultUni DefaultFun () -> [(Name, Type TyName DefaultUni ())]
constrTypes (Datatype _ _ xs _ cs) = [ (c, abstr ty) | VarDecl _ c ty <- cs ]
  where
    abstr ty = foldr (\ (TyVarDecl _ x k) -> TyForall () x k) ty xs

-- | Get the name and type of the match function for a given datatype.
matchType :: Datatype TyName Name DefaultUni DefaultFun () -> (Name, Type TyName DefaultUni ())
matchType (Datatype _ (TyVarDecl _ a _) xs m cs) = (m, matchType)
  where
    fvs = Set.fromList (a : [x | TyVarDecl _ x _ <- xs]) <>
          mconcat [ftvTy ty | VarDecl _ _ ty <- cs]
    pars = [TyVar () x | TyVarDecl _ x _ <- xs]
    dtyp = foldl (TyApp ()) (TyVar () a) pars
    matchType = abstr $ dtyp ->> TyForall () r Star (foldr ((->>) . conArg) (TyVar () r) cs)
      where r = freshenTyName fvs $ TyName $ Name "r" (toEnum 0)
            conArg (VarDecl _ _ ty) = setTarget ty
            setTarget (TyFun _ a b) = TyFun () a (setTarget b)
            setTarget _             = TyVar () r
    abstr ty = foldr (\ (TyVarDecl _ x k) -> TyForall () x k) ty xs

-- | Bind a datatype declaration in a generator.
bindDat :: Datatype TyName Name DefaultUni DefaultFun ()
        -> GenTm a
        -> GenTm a
bindDat dat@(Datatype _ (TyVarDecl _ a k) _ _ _) cont =
  bindTyName a k $
  local (\ e -> e { geDatas = Map.insert a dat (geDatas e) }) $
  foldr (uncurry bindTmName) cont (matchType dat : constrTypes dat)

-- | Bind a binding.
bindBind :: Binding TyName Name DefaultUni DefaultFun ()
         -> GenTm a
         -> GenTm a
bindBind (DatatypeBind _ dat)              = bindDat dat
bindBind (TermBind _ _ (VarDecl _ x ty) _) = bindTmName x ty
-- TODO: We should generate type bindings
bindBind _                                 = error "unreachable"

-- | Bind multiple bindings
bindBinds :: Foldable f => f (Binding TyName Name DefaultUni DefaultFun ()) -> GenTm a -> GenTm a
bindBinds = flip (foldr bindBind)
