-- | A "classic" (i.e. as seen in the specification) way to pretty-print PLC entities.

{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Pretty.Classic
    ( PrettyConfigClassic (..)
    , PrettyClassicBy
    , PrettyClassic
    , prettyClassicDef
    , prettyClassicDebug
    ) where

import           Language.PlutusCore.Lexer.Type
import           Language.PlutusCore.Name
import           Language.PlutusCore.Type
import           PlutusPrelude

import           Data.Functor.Foldable

-- | Configuration for the classic pretty-printing.
newtype PrettyConfigClassic configName = PrettyConfigClassic
    { _pccConfigName :: configName
    }

-- | The "classically pretty-printable" constraint.
type PrettyClassicBy configName = PrettyBy (PrettyConfigClassic configName)

type PrettyClassic = PrettyClassicBy PrettyConfigName

instance configName ~ PrettyConfigName => HasPrettyConfigName (PrettyConfigClassic configName) where
    toPrettyConfigName = _pccConfigName

instance PrettyBy (PrettyConfigClassic configName) (Kind a) where
    prettyBy _ = cata a where
        a TypeF{}             = "(type)"
        a (KindArrowF _ k k') = parens ("fun" <+> k <+> k')

instance PrettyBy (PrettyConfigClassic configName) (Constant a) where
    prettyBy _ (BuiltinInt _ i) = pretty i
    prettyBy _ (BuiltinBS _ b)  = prettyBytes b
    prettyBy _ (BuiltinStr _ s) = pretty s

instance PrettyBy (PrettyConfigClassic configName) (Builtin a) where
    prettyBy _ (BuiltinName    _ n) = pretty n
    prettyBy _ (DynBuiltinName _ n) = pretty n

instance PrettyClassicBy configName (tyname a) =>
        PrettyBy (PrettyConfigClassic configName) (Type tyname a) where
    prettyBy config = cata a where
        a (TyAppF _ t t')     = brackets (t <+> t')
        a (TyVarF _ n)        = prettyName n
        a (TyFunF _ t t')     = parens ("fun" <+> t <+> t')
        a (TyIFixF _ pat arg) = parens ("ifix" <+> pat <+> arg)
        a (TyForallF _ n k t) = parens ("all" <+> prettyName n <+> prettyBy config k <+> t)
        a (TyBuiltinF _ n)    = parens ("con" <+> pretty n)
        a (TyLamF _ n k t)    = parens ("lam" <+> prettyName n <+> prettyBy config k <+> t)

        prettyName = prettyBy config

instance (PrettyClassicBy configName (tyname a), PrettyClassicBy configName (name a)) =>
        PrettyBy (PrettyConfigClassic configName) (Term tyname name a) where
    prettyBy config = cata a where
        a (ConstantF _ b)      = parens' ("con" </> prettyBy config b)
        a (BuiltinF _ bi)      = parens' ("builtin" </> prettyBy config bi)
        a (ApplyF _ t t')      = brackets' (vsep' [t, t'])
        a (VarF _ n)           = prettyName n
        a (TyAbsF _ n k t)     = parens' ("abs" </> vsep' [prettyName n, prettyBy config k, t])
        a (TyInstF _ t ty)     = braces' (vsep' [t, prettyBy config ty])
        -- FIXME: only do the </> thing when there's a line break in the `vsep'` part?
        a (LamAbsF _ n ty t)   = parens' ("lam" </> vsep' [prettyName n, prettyBy config ty, t])
        a (UnwrapF _ t)        = parens' ("unwrap" </> t)
        a (IWrapF _ pat arg t) = parens' ("iwrap" </> vsep' [prettyBy config pat, prettyBy config arg, t])
        a (ErrorF _ ty)        = parens' ("error" </> prettyBy config ty)

        prettyName :: PrettyClassicBy configName n => n -> Doc ann
        prettyName = prettyBy config

instance PrettyClassicBy configName (Term tyname name a) =>
        PrettyBy (PrettyConfigClassic configName) (Program tyname name a) where
    prettyBy config (Program _ version term) =
        parens' $ "program" <+> pretty version <//> prettyBy config term

-- | Pretty-print a value in the default mode using the classic view.
prettyClassicDef :: PrettyClassic a => a -> Doc ann
prettyClassicDef = prettyBy $ PrettyConfigClassic defPrettyConfigName

-- | Pretty-print a value in the debug mode using the classic view.
prettyClassicDebug :: PrettyClassic a => a -> Doc ann
prettyClassicDebug = prettyBy $ PrettyConfigClassic debugPrettyConfigName
