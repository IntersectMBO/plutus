-- | A "classic" (i.e. as seen in the specification) way to pretty-print PLC entities.

{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Pretty.Classic
    ( PrettyConfigClassic (..)
    , PrettyClassicBy
    ) where

import           Language.PlutusCore.Lexer.Type
import           Language.PlutusCore.Name       (HasPrettyConfigName (..), PrettyConfigName)
import           Language.PlutusCore.Type
import           PlutusPrelude

import           Data.Functor.Foldable

-- | Configuration for the classic pretty-printing.
newtype PrettyConfigClassic configName = PrettyConfigClassic
    { _pccConfigName :: configName
    }

-- | The "classically pretty-printable" constraint.
type PrettyClassicBy configName = PrettyBy (PrettyConfigClassic configName)

instance configName ~ PrettyConfigName => HasPrettyConfigName (PrettyConfigClassic configName) where
    toPrettyConfigName = _pccConfigName

instance PrettyBy (PrettyConfigClassic configName) (Kind a) where
    prettyBy _ = cata a where
        a TypeF{}             = "(type)"
        a SizeF{}             = "(size)"
        a (KindArrowF _ k k') = parens ("fun" <+> k <+> k')

instance PrettyBy (PrettyConfigClassic configName) (Constant a) where
    prettyBy _ (BuiltinInt _ s i) = pretty s <+> "!" <+> pretty i
    prettyBy _ (BuiltinSize _ s)  = pretty s
    prettyBy _ (BuiltinBS _ s b)  = pretty s <+> "!" <+> prettyBytes b
    prettyBy _ (BuiltinName _ n)  = pretty n

instance PrettyClassicBy configName (tyname a) =>
        PrettyBy (PrettyConfigClassic configName) (Type tyname a) where
    prettyBy config = cata a where
        a (TyAppF _ t t')     = brackets (t <+> t')
        a (TyVarF _ n)        = prettyName n
        a (TyFunF _ t t')     = parens ("fun" <+> t <+> t')
        a (TyFixF _ n t)      = parens ("fix" <+> prettyName n <+> t)
        a (TyForallF _ n k t) = parens ("all" <+> prettyName n <+> prettyBy config k <+> t)
        a (TyBuiltinF _ n)    = parens ("con" <+> pretty n)
        a (TyIntF _ n)        = parens ("con" <+> pretty n)
        a (TyLamF _ n k t)    = parens ("lam" <+> prettyName n <+> prettyBy config k <+> t)

        prettyName = prettyBy config

instance (PrettyClassicBy configName (tyname a), PrettyClassicBy configName (name a)) =>
        PrettyBy (PrettyConfigClassic configName) (Term tyname name a) where
    prettyBy config = cata a where
        a (ConstantF _ b)    = parens' ("con" </> prettyBy config b)
        a (ApplyF _ t t')    = brackets' (vsep' [t, t'])
        a (VarF _ n)         = prettyName n
        a (TyAbsF _ n k t)   = parens' ("abs" </> vsep' [prettyName n, prettyBy config k, t])
        a (TyInstF _ t ty)   = braces' (vsep' [t, prettyBy config ty])
        -- FIXME: only do the </> thing when there's a line break in the `vsep'` part?
        a (LamAbsF _ n ty t) = parens' ("lam" </> vsep' [prettyName n, prettyBy config ty, t])
        a (UnwrapF _ t)      = parens' ("unwrap" </> t)
        a (WrapF _ n ty t)   = parens' ("wrap" </> vsep' [prettyName n, prettyBy config ty, t])
        a (ErrorF _ ty)      = parens' ("error" </> prettyBy config ty)

        prettyName :: PrettyClassicBy configName n => n -> Doc ann
        prettyName = prettyBy config

instance PrettyClassicBy configName (Term tyname name a) =>
        PrettyBy (PrettyConfigClassic configName) (Program tyname name a) where
    prettyBy config (Program _ version term) =
        parens' $ "program" <+> pretty version <//> prettyBy config term
