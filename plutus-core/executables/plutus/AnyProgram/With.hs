{-# LANGUAGE RankNTypes #-}
-- | BOILERPLATE needed to support Hasochism.
module AnyProgram.With where

import PlutusCore qualified as PLC
import UntypedPlutusCore qualified as UPLC
import PlutusCore.Pretty qualified as PLC

import Types
import Flat

withShowL :: forall s r. SLang s ->  (Show (FromLang s) => r) -> r
withShowL s r = case s of
    SPir sname sann -> withShowN sname $ withShowNT sname $ withShowA sann r
    SPlc sname sann -> withShowN sname $ withShowNT sname $ withShowA sann r
    SUplc sname sann -> withShowN sname $ withShowBinderN sname $ withShowA sann r
    SData -> error "not implemented yet"

withShowBinderN :: forall s r. SNaming s ->  (Show (UPLC.Binder (FromName s)) => r) -> r
withShowBinderN s r = case s of
    SName -> r
    SDeBruijn -> r
    SNamedDeBruijn -> r

withShowN :: forall s r. SNaming s ->  (Show (FromName s) => r) -> r
withShowN s r = case s of
    SName -> r
    SDeBruijn -> r
    SNamedDeBruijn -> r

withShowNT :: forall s r. SNaming s ->  (Show (FromNameTy s) => r) -> r
withShowNT s r = case s of
    SName -> r
    SDeBruijn -> r
    SNamedDeBruijn -> r

withShowA :: forall s r. SAnn s ->  (Show (FromAnn s) => r) -> r
withShowA s r = case s of
    SUnit -> r
    SSrcSpan_ -> r

withFlatL :: forall s r. SLang s ->  (Flat (FromLang s) => r) -> r
withFlatL s r = case s of
    SPir sname sann -> withFlatN sname $ withFlatNT sname $ withFlatA sann r
    SPlc sname sann -> withFlatN sname $ withFlatNT sname $ withFlatA sann r
    SUplc sname sann -> withFlatN sname $ withFlatBinderN sname $ withFlatA sann r
    SData -> error "not implemented yet"

withFlatBinderN :: forall s r. SNaming s ->  (Flat (UPLC.Binder (FromName s)) => r) -> r
withFlatBinderN s r = case s of
    SName -> r
    SDeBruijn -> r
    SNamedDeBruijn -> r

withFlatN :: forall s r. SNaming s ->  (Flat (FromName s) => r) -> r
withFlatN s r = case s of
    SName -> r
    SDeBruijn -> r
    SNamedDeBruijn -> r

withPrettyPlcL :: forall s r. SLang s -> (PLC.PrettyBy PLC.PrettyConfigPlc (FromLang s) => r) -> r
withPrettyPlcL s r = case s of
    SPir sname sann -> withPrettyPlcN sname $ withPrettyPlcNT sname $ withPrettyA sann $ r
    SPlc sname sann -> withPrettyPlcN sname $ withPrettyPlcNT sname $ withPrettyA sann $ r
    SUplc sname sann -> withPrettyPlcN sname $ withPrettyA sann $ r
    SData -> error "not implemented yet"

withPrettyA :: forall s r. SAnn s ->  (PLC.Pretty (FromAnn s) => r) -> r
withPrettyA s r = case s of
    SUnit -> r
    SSrcSpan_ -> r

withPrettyPlcN :: forall s r. SNaming s -> (( PLC.PrettyClassicBy PLC.PrettyConfigName (FromName s)
                                     , PLC.PrettyReadableBy PLC.PrettyConfigName (FromName s)) => r) -> r
withPrettyPlcN s r = case s of
    SName -> r
    SDeBruijn -> r
    SNamedDeBruijn -> r

withPrettyPlcNT :: forall s r. SNaming s -> (( PLC.PrettyClassicBy PLC.PrettyConfigName (FromNameTy s)
                                      , PLC.PrettyReadableBy PLC.PrettyConfigName (FromNameTy s)) => r) -> r
withPrettyPlcNT s r = case s of
    SName -> r
    SDeBruijn -> r
    SNamedDeBruijn -> r

withFlatNT :: forall s r. SNaming s ->  (Flat (FromNameTy s) => r) -> r
withFlatNT s r = case s of
    SName -> r
    SDeBruijn -> r
    SNamedDeBruijn -> r

withFlatA :: forall s r. SAnn s ->  (Flat (FromAnn s) => r) -> r
withFlatA s r = case s of
    SUnit -> r
    SSrcSpan_ -> r

withOrdA :: forall s r. SAnn s ->  ((Ord (FromAnn s)) => r) -> r
withOrdA s r = case s of
    SUnit -> r
    SSrcSpan_ -> r

withSemigroupA :: forall s r. SAnn s ->  ((Semigroup (FromAnn s)) => r) -> r
withSemigroupA s r = case s of
    SUnit -> r
    SSrcSpan_ -> r

instance Semigroup PLC.SrcSpan where
-- FIXME: stub

withMonoidA :: forall s r. SAnn s ->  ((Monoid (FromAnn s)) => r) -> r
withMonoidA s r = case s of
    SUnit -> r
    SSrcSpan_ -> r

instance Monoid PLC.SrcSpan where
-- FIXME: stub
