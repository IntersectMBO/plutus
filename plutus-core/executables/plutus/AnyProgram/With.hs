{-# LANGUAGE DataKinds                #-}
{-# LANGUAGE FlexibleInstances        #-}
{-# LANGUAGE MultiParamTypeClasses    #-}
{-# LANGUAGE PolyKinds                #-}
{-# LANGUAGE RankNTypes               #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE UndecidableSuperClasses  #-}
{-# OPTIONS_GHC -Wno-orphans #-}
-- | BOILERPLATE needed to support Hasochism.
-- See <https://homepages.inf.ed.ac.uk/slindley/papers/hasochism.pdf>
module AnyProgram.With where

import PlutusCore.Data qualified as PLC
import PlutusCore.Pretty as PLC
import UntypedPlutusCore qualified as UPLC

import Data.Kind (Constraint)
import Flat
import Types

-- for: (typeclass `compose` type)
type ComposeC :: forall a b. (b -> Constraint) -> (a -> b) -> a -> Constraint
class    constr (f x) => ComposeC constr f x
instance constr (f x) => ComposeC constr f x

withN :: forall constr s r
      . ( constr (FromName 'Name)
        , constr (FromName 'DeBruijn)
        , constr (FromName 'NamedDeBruijn)
        )
      => SNaming s -> ((constr (FromName s)) => r) -> r
withN s r = case s of
    SName          -> r
    SDeBruijn      -> r
    SNamedDeBruijn -> r

withNT :: forall constr s r
       . ( constr (FromNameTy 'Name)
         , constr (FromNameTy 'DeBruijn)
         , constr (FromNameTy 'NamedDeBruijn)
         )
       => SNaming s -> ((constr (FromNameTy s)) => r) -> r
withNT s r = case s of
    SName          -> r
    SDeBruijn      -> r
    SNamedDeBruijn -> r

withA :: forall constr s r
      . (constr (FromAnn 'Unit), constr (FromAnn 'TxSrcSpans))
      => SAnn s -> ((constr (FromAnn s)) => r) -> r
withA s r = case s of
    SUnit       -> r
    STxSrcSpans -> r

withFlatL :: forall s r. SLang s ->  (Flat (FromLang s) => r) -> r
withFlatL s r = case s of
    SPir sname sann -> withN @Flat sname $ withNT @Flat sname $ withA @Flat sann r
    SPlc sname sann -> withN @Flat sname $ withNT @Flat sname $ withA @Flat sann r
    SUplc sname sann -> withN @Flat sname $ withN @(ComposeC Flat UPLC.Binder) sname $
                       withA @Flat sann r
    SData -> error "Flat is not available for Data"

withShowL :: forall s r. SLang s ->  (Show (FromLang s) => r) -> r
withShowL s r = case s of
    SPir sname sann -> withN @Show sname $ withNT @Show sname $ withA @Show sann r
    SPlc sname sann -> withN @Show sname $ withNT @Show sname $ withA @Show sann r
    SUplc sname sann -> withN @Show sname $ withN @(ComposeC Show UPLC.Binder) sname $
                       withA @Show sann r
    SData -> r

withPrettyPlcL :: forall s r. SLang s -> (PrettyBy PrettyConfigPlc (FromLang s) => r) -> r
withPrettyPlcL s r = case s of
    SPir sname sann -> withN @PrettyClassic sname $ withN @PrettyReadable sname $
                      withNT @PrettyClassic sname $ withNT @PrettyReadable sname $
                      withA @Pretty sann r
    SPlc sname sann -> withN @PrettyClassic sname $ withN @PrettyReadable sname $
                      withNT @PrettyClassic sname $ withNT @PrettyReadable sname $
                      withA @Pretty sann r
    SUplc sname sann -> withN @PrettyClassic sname $ withN @PrettyReadable sname $
                       withA @Pretty sann r
    SData -> r

-- a dummy to make `withPrettyPlcL` work also with `Data`
instance PrettyBy PrettyConfigPlc PLC.Data where
    prettyBy _           = pretty
