-- | A "classic" (i.e. as seen in the specification) way to pretty-print PLC entities.

{-# OPTIONS_GHC -fno-warn-orphans #-}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Erasure.Untyped.Instance.Pretty.Classic () where

import           PlutusPrelude

import           Language.PlutusCore.Erasure.Untyped.Instance.Pretty.Common ()
import           Language.PlutusCore.Erasure.Untyped.Instance.Recursive
import           Language.PlutusCore.Erasure.Untyped.Term
import           Language.PlutusCore.Pretty.Classic
import           Language.PlutusCore.Pretty.Utils

import           Data.Functor.Foldable

instance PrettyBy (PrettyConfigClassic configName) (Constant a) where
    prettyBy _ (BuiltinInt _ i) = pretty i
    prettyBy _ (BuiltinBS _ b)  = prettyBytes b
    prettyBy _ (BuiltinStr _ s) = pretty s

instance PrettyBy (PrettyConfigClassic configName) (Builtin a) where
    prettyBy _ (BuiltinName    _ n) = pretty n
    prettyBy _ (DynBuiltinName _ n) = pretty n

instance PrettyClassicBy configName (name a) =>
        PrettyBy (PrettyConfigClassic configName) (Term name a) where
    prettyBy config = cata a where
        a (ConstantF _ b) = parens' ("con" </> prettyBy config b)
        a (BuiltinF _ bi) = parens' ("builtin" </> prettyBy config bi)
        a (ApplyF _ t t') = brackets' (vsep' [t, t'])
        a (VarF _ n)      = prettyName n
        a (LamAbsF _ n t) = parens' ("lam" </> vsep' [prettyName n, t])
        a (ErrorF _)      = "error"
        a (PruneF _ _)    = "<prune>"

        prettyName :: PrettyClassicBy configName n => n -> Doc ann
        prettyName = prettyBy config

instance PrettyClassicBy configName (Term name a) =>
        PrettyBy (PrettyConfigClassic configName) (Program name a) where
    prettyBy config (Program _ version term) =
        parens' $ "program" <+> pretty version <//> prettyBy config term
