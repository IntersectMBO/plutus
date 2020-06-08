{-# LANGUAGE DeriveAnyClass         #-}
{-# LANGUAGE DerivingStrategies     #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}
-- appears in the generated instances
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

module Language.PlutusCore.Error
    ( ParseError (..)
    , AsParseError (..)
    , NormCheckError (..)
    , AsNormCheckError (..)
    , UniqueError (..)
    , AsUniqueError (..)
    , BuiltinError (..)
    , InternalTypeError (..)
    , AsInternalTypeError (..)
    , TypeError (..)
    , AsTypeError (..)
    , Error (..)
    , AsError (..)
    , throwingEither
    ) where

import           PlutusPrelude

import           Language.PlutusCore.Core
import           Language.PlutusCore.Lexer.Type
import           Language.PlutusCore.Name
import           Language.PlutusCore.Pretty
import           Language.PlutusCore.Universe

import           Control.Lens                       hiding (use)
import           Control.Monad.Error.Lens
import           Control.Monad.Except
import qualified Data.Text                          as T
import           Data.Text.Prettyprint.Doc.Internal (Doc (Text))

{- Note [Annotations and equality]
Equality of two errors DOES DEPEND on their annotations.
So feel free to use @deriving Eq@ for errors.
This is because even though we do care about errors having an 'Eq' instance (which is required for
example by tests that do checks like @resOrErr == Right res@), we don't care much about actually
checking errors for equality and @deriving Eq@ saves us a lot of boilerplate.
-}

-- | Lifts an 'Either' into an error context where we can embed the 'Left' value into the error.
throwingEither :: MonadError e m => AReview e t -> Either t a -> m a
throwingEither r e = case e of
    Left t  -> throwing r t
    Right v -> pure v

-- | An error encountered during parsing.
data ParseError ann
    = LexErr String
    | Unexpected (Token ann)
    deriving (Show, Eq, Generic, NFData)
makeClassyPrisms ''ParseError

data UniqueError ann
    = MultiplyDefined Unique ann ann
    | IncoherentUsage Unique ann ann
    | FreeVariable Unique ann
    deriving (Show, Eq, Generic, NFData)
makeClassyPrisms ''UniqueError

data NormCheckError tyname name uni ann
    = BadType ann (Type tyname uni ann) T.Text
    | BadTerm ann (Term tyname name uni ann) T.Text
    deriving (Show, Generic, NFData)
deriving instance
    ( HasUniques (Term tyname name uni ann)
    , GEq uni, Closed uni, uni `Everywhere` Eq
    , Eq ann
    ) => Eq (NormCheckError tyname name uni ann)
makeClassyPrisms ''NormCheckError

-- TODO: split into type/other errors
data BuiltinError ann =
    UnknownDynamicBuiltinName ann DynamicBuiltinName
    | BuiltinUnderInstantiated  ann BuiltinName
    | BuiltinOverInstantiated   ann BuiltinName
    | BuiltinUnderApplied       ann BuiltinName
    | BuiltinOverApplied        ann BuiltinName
    | BadTypeScheme             ann BuiltinName
    deriving (Show, Eq, Generic, NFData)
makeClassyPrisms ''BuiltinError

-- FIXME: do something else
annOf :: BuiltinError ann -> ann
annOf (UnknownDynamicBuiltinName ann _) = ann
annOf (BuiltinUnderInstantiated  ann _) = ann
annOf (BuiltinOverInstantiated   ann _) = ann
annOf (BuiltinUnderApplied       ann _) = ann
annOf (BuiltinOverApplied        ann _) = ann
annOf (BadTypeScheme             ann _) = ann

-- | An internal error occurred during type checking.
data InternalTypeError uni ann
    = OpenTypeOfBuiltin (Type TyName uni ()) BuiltinName
    deriving (Show, Eq, Generic, NFData)
makeClassyPrisms ''InternalTypeError

data TypeError uni ann
    = KindMismatch ann (Type TyName uni ()) (Kind ())  (Kind ())
    | TypeMismatch ann
        (Term TyName Name uni ())
        (Type TyName uni ())
        (Normalized (Type TyName uni ()))
    | InternalTypeErrorE ann (InternalTypeError uni ann)
    | FreeTypeVariableE ann TyName
    | FreeVariableE ann Name
    | BuiltinTypeErrorE (BuiltinError ann)
    deriving (Show, Eq, Generic, NFData)
makeClassyPrisms ''TypeError

data Error uni ann
    = ParseErrorE (ParseError ann)
    | UniqueCoherencyErrorE (UniqueError ann)
    | TypeErrorE (TypeError uni ann)
    | NormCheckErrorE (NormCheckError TyName Name uni ann)
    | BuiltinErrorE (BuiltinError ann)
    deriving (Show, Eq, Generic, NFData)
makeClassyPrisms ''Error

instance AsParseError (Error uni ann) ann where
    _ParseError = _ParseErrorE

instance AsUniqueError (Error uni ann) ann where
    _UniqueError = _UniqueCoherencyErrorE

instance AsTypeError (Error uni ann) uni ann where
    _TypeError = _TypeErrorE

instance (tyname ~ TyName, name ~ Name) =>
            AsNormCheckError (Error uni ann) tyname name uni ann where
    _NormCheckError = _NormCheckErrorE

asInternalError :: Doc ann -> Doc ann
asInternalError doc =
    "An internal error has occurred:" <+> doc <> hardline <>
    "Please report this as a bug."

instance Pretty ann => Pretty (ParseError ann) where
    pretty (LexErr s)     = "Lexical error:" <+> Text (length s) (T.pack s)
    pretty (Unexpected t) = "Unexpected" <+> squotes (pretty t) <+> "at" <+> pretty (tkLoc t)

instance Pretty ann => Pretty (UniqueError ann) where
    pretty (MultiplyDefined u def redef) =
        "Variable" <+> pretty u <+> "defined at" <+> pretty def <+>
        "is redefined at" <+> pretty redef
    pretty (IncoherentUsage u def use) =
        "Variable" <+> pretty u <+> "defined at" <+> pretty def <+>
        "is used in a different scope at" <+> pretty use
    pretty (FreeVariable u use) =
        "Variable" <+> pretty u <+> "is free at" <+> pretty use

instance ( Pretty ann
         , PrettyBy config (Type tyname uni ann)
         , PrettyBy config (Term tyname name uni ann)
         ) => PrettyBy config (NormCheckError tyname name uni ann) where
    prettyBy config (BadType ann ty expct) =
        "Malformed type at" <+> pretty ann <>
        ". Type" <+>  squotes (prettyBy config ty) <+>
        "is not a" <+> pretty expct <> "."
    prettyBy config (BadTerm ann t expct) =
        "Malformed term at" <+> pretty ann <>
        ". Term" <+> squotes (prettyBy config t) <+>
        "is not a" <+> pretty expct <> "."

instance Pretty ann => Pretty (BuiltinError ann) where
    pretty (UnknownDynamicBuiltinName _ann dbn) = "Unknown dynamic built-in name: " <+> pretty dbn
    pretty (BuiltinUnderInstantiated  _ann bn)  = "Built-in function underinstantiated: " <+> pretty bn
    pretty (BuiltinOverInstantiated   _ann bn)  = "Built-in function overinstantiated: " <+> pretty bn
    pretty (BuiltinUnderApplied       _ann bn)  = "Built-in function underapplied: " <+> pretty bn
    pretty (BuiltinOverApplied        _ann bn)  = "Built-in function overapplied: " <+> pretty bn
    pretty (BadTypeScheme             _ann bn)  = "Malformed type scheme for: " <+> pretty bn
-- FIXME: do this properly; maybe also add more info, like the number of args expected and found


instance GShow uni => PrettyBy PrettyConfigPlc (InternalTypeError uni ann) where
    prettyBy config (OpenTypeOfBuiltin ty bi)        =
        asInternalError $
            "The type" <+> prettyBy config ty <+>
            "of the" <+> prettyBy config bi <+>
            "built-in is open"

instance (GShow uni, Closed uni, uni `Everywhere` PrettyConst,  Pretty ann) =>
            PrettyBy PrettyConfigPlc (TypeError uni ann) where
    prettyBy config (KindMismatch ann ty k k')          =
        "Kind mismatch at" <+> pretty ann <+>
        "in type" <+> squotes (prettyBy config ty) <>
        ". Expected kind" <+> squotes (prettyBy config k) <+>
        ", found kind" <+> squotes (prettyBy config k')
    prettyBy config (TypeMismatch ann t ty ty')         =
        "Type mismatch at" <+> pretty ann <>
        (if _pcpoCondensedErrors (_pcpOptions config) == CondensedErrorsYes
            then mempty
            else " in term" <> hardline <> indent 2 (squotes (prettyBy config t)) <> ".") <>
        hardline <>
        "Expected type" <> hardline <> indent 2 (squotes (prettyBy config ty)) <>
        "," <> hardline <>
        "found type" <> hardline <> indent 2 (squotes (prettyBy config ty'))
    prettyBy config (FreeTypeVariableE ann name)          =
        "Free type variable at " <+> pretty ann <+> ": " <+> prettyBy config name
    prettyBy config (FreeVariableE ann name)              =
        "Free variable at " <+> pretty ann <+> ": " <+> prettyBy config name
    prettyBy config (InternalTypeErrorE ann err)        =
        prettyBy config err <> hardline <>
        "Error location:" <+> pretty ann
    prettyBy _ (BuiltinTypeErrorE err) =
        pretty err <> hardline <>
        "Error location:" <+> pretty (annOf err)

instance (GShow uni, Closed uni, uni `Everywhere` PrettyConst, Pretty ann) =>
            PrettyBy PrettyConfigPlc (Error uni ann) where
    prettyBy _      (ParseErrorE e)           = pretty e
    prettyBy _      (UniqueCoherencyErrorE e) = pretty e
    prettyBy config (TypeErrorE e)            = prettyBy config e
    prettyBy config (NormCheckErrorE e)       = prettyBy config e
    prettyBy _      (BuiltinErrorE e)         = pretty e
