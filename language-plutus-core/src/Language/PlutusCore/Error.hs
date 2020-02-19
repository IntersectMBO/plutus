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
    , UnknownDynamicBuiltinNameError (..)
    , AsUnknownDynamicBuiltinNameError (..)
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
    | Overflow ann Natural Integer
    deriving (Show, Eq, Generic, NFData)
makeClassyPrisms ''ParseError

data UniqueError ann
    = MultiplyDefined Unique ann ann
    | IncoherentUsage Unique ann ann
    | FreeVariable Unique ann
    deriving (Show, Eq, Generic, NFData)
makeClassyPrisms ''UniqueError

data NormCheckError tyname name ann
    = BadType ann (Type tyname ann) T.Text
    | BadTerm ann (Term tyname name ann) T.Text
    deriving (Show, Generic, NFData)
deriving instance (Eq ann, HasUniques (Term tyname name ann)) => Eq (NormCheckError tyname name ann)
makeClassyPrisms ''NormCheckError

-- | This error is returned whenever scope resolution of a 'DynamicBuiltinName' fails.
newtype UnknownDynamicBuiltinNameError
    = UnknownDynamicBuiltinNameErrorE DynamicBuiltinName
    deriving (Show, Eq, Generic)
    deriving newtype (NFData)
makeClassyPrisms ''UnknownDynamicBuiltinNameError

-- | An internal error occurred during type checking.
data InternalTypeError ann
    = OpenTypeOfBuiltin (Type TyName ()) (Builtin ())
    deriving (Show, Eq, Generic, NFData)
makeClassyPrisms ''InternalTypeError

data TypeError ann
    = KindMismatch ann (Type TyName ()) (Kind ()) (Kind ())
    | TypeMismatch ann
        (Term TyName Name ())
        (Type TyName ())
        (Normalized (Type TyName ()))
    | UnknownDynamicBuiltinName ann UnknownDynamicBuiltinNameError
    | InternalTypeErrorE ann (InternalTypeError ann)
    | FreeTypeVariableE (TyName ann)
    | FreeVariableE (Name ann)
    | OutOfGas
    deriving (Show, Eq, Generic, NFData)
makeClassyPrisms ''TypeError

data Error ann
    = ParseErrorE (ParseError ann)
    | UniqueCoherencyErrorE (UniqueError ann)
    | TypeErrorE (TypeError ann)
    | NormCheckErrorE (NormCheckError TyName Name ann)
    deriving (Show, Eq, Generic, NFData)
makeClassyPrisms ''Error

instance AsParseError (Error ann) ann where
    _ParseError = _ParseErrorE

instance AsUniqueError (Error ann) ann where
    _UniqueError = _UniqueCoherencyErrorE

instance AsTypeError (Error ann) ann where
    _TypeError = _TypeErrorE

instance (tyname ~ TyName, name ~ Name) =>
            AsNormCheckError (Error ann) tyname name ann where
    _NormCheckError = _NormCheckErrorE

asInternalError :: Doc ann -> Doc ann
asInternalError doc =
    "An internal error has occurred:" <+> doc <> hardline <>
    "Please report this as a bug."

instance Pretty ann => Pretty (ParseError ann) where
    pretty (LexErr s)         = "Lexical error:" <+> Text (length s) (T.pack s)
    pretty (Unexpected t)     = "Unexpected" <+> squotes (pretty t) <+> "at" <+> pretty (tkLoc t)
    pretty (Overflow ann _ _) = "Integer overflow at" <+> pretty ann <> "."

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
         , PrettyBy config (Type tyname ann)
         , PrettyBy config (Term tyname name ann)
         ) => PrettyBy config (NormCheckError tyname name ann) where
    prettyBy config (BadType ann ty expct) =
        "Malformed type at" <+> pretty ann <>
        ". Type" <+>  squotes (prettyBy config ty) <+>
        "is not a" <+> pretty expct <> "."
    prettyBy config (BadTerm ann t expct) =
        "Malformed term at" <+> pretty ann <>
        ". Term" <+> squotes (prettyBy config t) <+>
        "is not a" <+> pretty expct <> "."

instance Pretty UnknownDynamicBuiltinNameError where
    pretty (UnknownDynamicBuiltinNameErrorE dbn) =
        "Scope resolution failed on a dynamic built-in name:" <+> pretty dbn

instance PrettyBy PrettyConfigPlc (InternalTypeError ann) where
    prettyBy config (OpenTypeOfBuiltin ty bi)        =
        asInternalError $
            "The type" <+> prettyBy config ty <+>
            "of the" <+> prettyBy config bi <+>
            "built-in is open"

instance Pretty ann => PrettyBy PrettyConfigPlc (TypeError ann) where
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
    prettyBy config (FreeTypeVariableE name)          =
        "Free type variable:" <+> prettyBy config name
    prettyBy config (FreeVariableE name)              =
        "Free variable:" <+> prettyBy config name
    prettyBy config (InternalTypeErrorE ann err)        =
        prettyBy config err <> hardline <>
        "Error location:" <+> pretty ann
    prettyBy _      (UnknownDynamicBuiltinName ann err) =
        "Unknown dynamic built-in name at" <+> pretty ann <>
        ":" <+> pretty err
    prettyBy _      OutOfGas                          = "Type checker ran out of gas."

instance Pretty ann => PrettyBy PrettyConfigPlc (Error ann) where
    prettyBy _      (ParseErrorE e)           = pretty e
    prettyBy _      (UniqueCoherencyErrorE e) = pretty e
    prettyBy config (TypeErrorE e)            = prettyBy config e
    prettyBy config (NormCheckErrorE e)       = prettyBy config e
