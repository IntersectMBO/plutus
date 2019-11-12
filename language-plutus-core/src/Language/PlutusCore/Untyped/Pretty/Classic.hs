-- | A "classic" (i.e. as seen in the specification) way to pretty-print PLC entities.

{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}

module Language.PlutusCore.Untyped.Pretty.Classic
    ( PrettyConfigClassic (..)
    , PrettyClassicBy
    , PrettyClassic
    , prettyClassicDef
    , prettyClassicDebug
    ) where

import           Language.PlutusCore.Lexer.Type
import           Language.PlutusCore.Name
import           Language.PlutusCore.Untyped.Term
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
        a (ConstantF _ b)      = parens' ("con" </> prettyBy config b)
        a (BuiltinF _ bi)      = parens' ("builtin" </> prettyBy config bi)
        a (ApplyF _ t t')      = brackets' (vsep' [t, t'])
        a (VarF _ n)           = prettyName n
        a (LamAbsF _ n t)      = parens' ("lam" </> vsep' [prettyName n, t])
        a (ErrorF _)           = parens' "error"

        prettyName :: PrettyClassicBy configName n => n -> Doc ann
        prettyName = prettyBy config

instance PrettyClassicBy configName (Term name a) =>
        PrettyBy (PrettyConfigClassic configName) (Program name a) where
    prettyBy config (Program _ version term) =
        parens' $ "program" <+> pretty version <//> prettyBy config term

-- | Pretty-print a value in the default mode using the classic view.
prettyClassicDef :: PrettyClassic a => a -> Doc ann
prettyClassicDef = prettyBy $ PrettyConfigClassic defPrettyConfigName

-- | Pretty-print a value in the debug mode using the classic view.
prettyClassicDebug :: PrettyClassic a => a -> Doc ann
prettyClassicDebug = prettyBy $ PrettyConfigClassic debugPrettyConfigName
