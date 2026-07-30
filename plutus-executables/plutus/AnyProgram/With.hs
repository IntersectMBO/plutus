{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -Wno-orphans #-}

{-| BOILERPLATE needed to support Hasochism.
See <https://homepages.inf.ed.ac.uk/slindley/papers/hasochism.pdf> -}
module AnyProgram.With where

import PlutusCore qualified as PLC
import PlutusCore.Data qualified as PLC
import PlutusCore.Pretty as PLC
import PlutusIR qualified as PIR
import UntypedPlutusCore qualified as UPLC

import Data.Kind (Constraint)
import Types

-- for: (typeclass `compose` type)
type ComposeC :: forall a b. (b -> Constraint) -> (a -> b) -> a -> Constraint
class constr (f x) => ComposeC constr f x
instance constr (f x) => ComposeC constr f x

type UnitC :: forall a. a -> Constraint
class UnitC x
instance UnitC x

type AndC :: forall a. (a -> Constraint) -> (a -> Constraint) -> a -> Constraint
class (constr1 x, constr2 x) => AndC constr1 constr2 x
instance (constr1 x, constr2 x) => AndC constr1 constr2 x

withN
  :: forall constr s r
   . ( constr (FromName 'Name)
     , constr (FromName 'DeBruijn)
     , constr (FromName 'NamedDeBruijn)
     )
  => SNaming s -> (constr (FromName s) => r) -> r
withN s r = case s of
  SName -> r
  SDeBruijn -> r
  SNamedDeBruijn -> r

withNT
  :: forall constr s r
   . ( constr (FromNameTy 'Name)
     , constr (FromNameTy 'DeBruijn)
     , constr (FromNameTy 'NamedDeBruijn)
     )
  => SNaming s -> (constr (FromNameTy s) => r) -> r
withNT s r = case s of
  SName -> r
  SDeBruijn -> r
  SNamedDeBruijn -> r

withA
  :: forall constr s r
   . (constr (FromAnn 'Unit), constr (FromAnn 'TxSrcSpans))
  => SAnn s -> (constr (FromAnn s) => r) -> r
withA s r = case s of
  SUnit -> r
  STxSrcSpans -> r

withLangGeneral
  :: forall constrTyName constrBinder constrName constrAnn constr s r
   . ( constrTyName (FromNameTy 'Name)
     , constrTyName (FromNameTy 'DeBruijn)
     , constrTyName (FromNameTy 'NamedDeBruijn)
     , constrBinder (UPLC.Binder UPLC.Name)
     , constrBinder (UPLC.Binder UPLC.DeBruijn)
     , constrBinder (UPLC.Binder UPLC.NamedDeBruijn)
     , constrName (FromName 'Name)
     , constrName (FromName 'DeBruijn)
     , constrName (FromName 'NamedDeBruijn)
     , constrAnn (FromAnn 'Unit)
     , constrAnn (FromAnn 'TxSrcSpans)
     , ( forall tyname name ann
          . (constrTyName tyname, constrName name, constrAnn ann)
         => constr (PIR.Program tyname name UPLC.DefaultUni UPLC.DefaultFun ann)
       )
     , ( forall tyname name ann
          . (constrTyName tyname, constrName name, constrAnn ann)
         => constr (PLC.Program tyname name UPLC.DefaultUni UPLC.DefaultFun ann)
       )
     , ( forall name ann
          . (constrBinder (UPLC.Binder name), constrName name, constrAnn ann)
         => constr (UPLC.UnrestrictedProgram name UPLC.DefaultUni UPLC.DefaultFun ann)
       )
     )
  => SLang s -> (constr (FromLang s) => r) -> r
withLangGeneral s r = case s of
  SPir sname sann ->
    withNT @constrTyName sname $
      withN @constrName sname $
        withA @constrAnn sann r
  SPlc sname sann ->
    withNT @constrTyName sname $
      withN @constrName sname $
        withA @constrAnn sann r
  SUplc sname sann ->
    withN @(ComposeC constrBinder UPLC.Binder) sname $
      withN @constrName sname $
        withA @constrAnn sann r
  SData -> error "not implemented yet"

withLang
  :: forall constr s r
   . ( constr (FromNameTy 'Name)
     , constr (FromNameTy 'DeBruijn)
     , constr (FromNameTy 'NamedDeBruijn)
     , constr (UPLC.Binder UPLC.Name)
     , constr (UPLC.Binder UPLC.DeBruijn)
     , constr (UPLC.Binder UPLC.NamedDeBruijn)
     , constr (FromName 'Name)
     , constr (FromName 'DeBruijn)
     , constr (FromName 'NamedDeBruijn)
     , constr (FromAnn 'Unit)
     , constr (FromAnn 'TxSrcSpans)
     , ( forall tyname name ann
          . (constr tyname, constr name, constr ann)
         => constr (PIR.Program tyname name UPLC.DefaultUni UPLC.DefaultFun ann)
       )
     , ( forall tyname name ann
          . (constr tyname, constr name, constr ann)
         => constr (PLC.Program tyname name UPLC.DefaultUni UPLC.DefaultFun ann)
       )
     , ( forall name ann
          . (constr (UPLC.Binder name), constr name, constr ann)
         => constr (UPLC.UnrestrictedProgram name UPLC.DefaultUni UPLC.DefaultFun ann)
       )
     )
  => SLang s -> (constr (FromLang s) => r) -> r
withLang = withLangGeneral @constr @constr @constr @constr @constr

withPrettyPlcL :: forall s r. SLang s -> (PrettyPlc (FromLang s) => r) -> r
withPrettyPlcL =
  withLangGeneral
    @(PrettyClassic `AndC` PrettyReadable)
    @UnitC
    @(PrettyClassic `AndC` PrettyReadable)
    @Pretty
    @PrettyPlc

instance PrettyBy PrettyConfigPlc PLC.Data
