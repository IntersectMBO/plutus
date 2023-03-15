{-# LANGUAGE DeriveAnyClass         #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
-- appears in the generated instances

module PlutusCore.Error
    ( ParserError (..)
    , AsParserErrorBundle (..)
    , ParserErrorBundle (..)
    , NormCheckError (..)
    , AsNormCheckError (..)
    , UniqueError (..)
    , AsUniqueError (..)
    , TypeError (..)
    , AsTypeError (..)
    , FreeVariableError (..)
    , AsFreeVariableError (..)
    , Error (..)
    , AsError (..)
    , throwingEither
    , ShowErrorComponent (..)
    ) where

import PlutusPrelude

import PlutusCore.Core
import PlutusCore.DeBruijn.Internal
import PlutusCore.Name
import PlutusCore.Pretty

import Control.Lens hiding (use)
import Control.Monad.Error.Lens
import Control.Monad.Except
import Data.Text qualified as T
import Prettyprinter (hardline, hsep, indent, squotes, (<+>))
import Text.Megaparsec as M
import Universe

-- | Lifts an 'Either' into an error context where we can embed the 'Left' value into the error.
throwingEither :: MonadError e m => AReview e t -> Either t a -> m a
throwingEither r e = case e of
    Left t  -> throwing r t
    Right v -> pure v

-- | An error encountered during parsing.
data ParserError
    = UnknownBuiltinType !T.Text !SourcePos
    | BuiltinTypeNotAStar !T.Text !SourcePos
    | UnknownBuiltinFunction !T.Text !SourcePos ![T.Text]
    | InvalidBuiltinConstant !T.Text !T.Text !SourcePos
    | InvalidData !T.Text !SourcePos
    deriving stock (Eq, Ord, Generic)
    deriving anyclass (NFData)

instance Show ParserError
    where
      show = show . pretty

data UniqueError ann
    = MultiplyDefined !Unique !ann !ann
    | IncoherentUsage !Unique !ann !ann
    | FreeVariable !Unique !ann
    deriving stock (Show, Eq, Generic, Functor)
    deriving anyclass (NFData)

data NormCheckError tyname name uni fun ann
    = BadType !ann !(Type tyname uni ann) !T.Text
    | BadTerm !ann !(Term tyname name uni fun ann) !T.Text
    deriving stock (Show, Functor, Generic)
    deriving anyclass (NFData)
deriving stock instance
    ( Eq (Term tyname name uni fun ann)
    , Eq (Type tyname uni ann)
    , GEq uni, Closed uni, uni `Everywhere` Eq
    , Eq fun, Eq ann
    ) => Eq (NormCheckError tyname name uni fun ann)

data TypeError term uni fun ann
    = KindMismatch !ann !(Type TyName uni ()) !(Kind ()) !(Kind ())
    | TypeMismatch !ann
        !term
        !(Type TyName uni ())
        -- ^ Expected type
        !(Normalized (Type TyName uni ()))
        -- ^ Actual type
    | TyNameMismatch !ann !TyName !TyName
    | NameMismatch !ann !Name !Name
    | FreeTypeVariableE !ann !TyName
    | FreeVariableE !ann !Name
    | UnknownBuiltinFunctionE !ann !fun
    deriving stock (Show, Eq, Generic, Functor)
    deriving anyclass (NFData)

-- Make a custom data type and wrap @ParseErrorBundle@ in it so I can use @makeClassyPrisms@
-- on @ParseErrorBundle@.
data ParserErrorBundle
    = ParseErrorB !(ParseErrorBundle T.Text ParserError)
    deriving stock (Show, Eq, Generic)
    deriving anyclass (NFData)

instance Pretty ParserErrorBundle where
    pretty (ParseErrorB err) = pretty $ errorBundlePretty err

data Error uni fun ann
    = ParseErrorE !ParserErrorBundle
    | UniqueCoherencyErrorE !(UniqueError ann)
    | TypeErrorE !(TypeError (Term TyName Name uni fun ()) uni fun ann)
    | NormCheckErrorE !(NormCheckError TyName Name uni fun ann)
    | FreeVariableErrorE !FreeVariableError
    deriving stock (Eq, Generic, Functor)
    deriving anyclass (NFData)
deriving stock instance
    (Show fun, Show ann, Closed uni, Everywhere uni Show, GShow uni, Show ParserError) =>
        Show (Error uni fun ann)

instance Pretty SourcePos where
    pretty = pretty . sourcePosPretty

instance Pretty ParserError where
    pretty (UnknownBuiltinType s loc)       =
        "Unknown built-in type" <+> squotes (pretty s) <+> "at" <+> pretty loc
    pretty (BuiltinTypeNotAStar ty loc)     =
        "Expected a type of kind star (to later parse a constant), but got:" <+>
            squotes (pretty ty) <+> "at" <+> pretty loc
    pretty (UnknownBuiltinFunction s loc lBuiltin)   =
        "Unknown built-in function" <+> squotes (pretty s) <+> "at" <+> pretty loc <+>
            ". Parsable functions are " <+> pretty lBuiltin
    pretty (InvalidBuiltinConstant c s loc) =
        "Invalid constant" <+> squotes (pretty c) <+> "of type" <+> squotes (pretty s) <+> "at" <+>
            pretty loc
    pretty (InvalidData err loc) = "Invalid data:" <+> squotes (pretty err) <+> "at" <+> pretty loc

instance ShowErrorComponent ParserError where
    showErrorComponent = show . pretty

instance Pretty ann => Pretty (UniqueError ann) where
    pretty (MultiplyDefined u defd redefd) =
        "Variable" <+> pretty u <+> "defined at" <+> pretty defd <+>
        "is redefined at" <+> pretty redefd
    pretty (IncoherentUsage u defd use) =
        "Variable" <+> pretty u <+> "defined at" <+> pretty defd <+>
        "is used in a different scope at" <+> pretty use
    pretty (FreeVariable u use) =
        "Variable" <+> pretty u <+> "is free at" <+> pretty use

instance ( Pretty ann
         , PrettyBy config (Type tyname uni ann)
         , PrettyBy config (Term tyname name uni fun ann)
         ) => PrettyBy config (NormCheckError tyname name uni fun ann) where
    prettyBy config (BadType ann ty expct) =
        "Malformed type at" <+> pretty ann <>
        ". Type" <+>  squotes (prettyBy config ty) <+>
        "is not a" <+> pretty expct <> "."
    prettyBy config (BadTerm ann t expct) =
        "Malformed term at" <+> pretty ann <>
        ". Term" <+> squotes (prettyBy config t) <+>
        "is not a" <+> pretty expct <> "."

instance
        ( Pretty term
        , Pretty (SomeTypeIn uni)
        , Closed uni, uni `Everywhere` PrettyConst
        , Pretty fun
        , Pretty ann
        ) => PrettyBy PrettyConfigPlc (TypeError term uni fun ann) where
    prettyBy config (KindMismatch ann ty k k')          =
        "Kind mismatch at" <+> pretty ann <+>
        "in type" <+> squotes (prettyBy config ty) <>
        ". Expected kind" <+> squotes (prettyBy config k) <+>
        ", found kind" <+> squotes (prettyBy config k')
    prettyBy config (TypeMismatch ann t ty ty')         =
        "Type mismatch at" <+> pretty ann <>
        (if _pcpoCondensedErrors (_pcpOptions config) == CondensedErrorsYes
            then mempty
            -- TODO: we should use prettyBy here but the problem is
            -- that `instance PrettyClassic PIR.Term` whereas `instance PrettyPLC PLC.Term`
            else " in term" <> hardline <> indent 2 (squotes (pretty t)) <> ".") <>
        hardline <>
        "Expected type" <> hardline <> indent 2 (squotes (prettyBy config ty)) <>
        "," <> hardline <>
        "found type" <> hardline <> indent 2 (squotes (prettyBy config ty'))
    prettyBy config (FreeTypeVariableE ann name)          =
        "Free type variable at " <+> pretty ann <+> ": " <+> prettyBy config name
    prettyBy config (FreeVariableE ann name)              =
        "Free variable at " <+> pretty ann <+> ": " <+> prettyBy config name
    prettyBy _ (UnknownBuiltinFunctionE ann fun) =
        "An unknown built-in function at" <+> pretty ann <> ":" <+> pretty fun
    prettyBy _ (TyNameMismatch ann name1 name2) = hsep
        [ "Type-level name mismatch at"
        , pretty ann <> ":"
        , pretty $ name1 ^. theText
        , "is in scope, but"
        , pretty $ name2 ^. theText
        , "having the same Unique"
        , pretty $ name1 ^. theUnique
        , "is attempted to be referenced"
        ]
    prettyBy _ (NameMismatch ann name1 name2) = hsep
        [ "Term-level name mismatch at"
        , pretty ann <> ":"
        , pretty $ name1 ^. theText
        , "is in scope, but"
        , pretty $ name2 ^. theText
        , "having the same Unique"
        , pretty $ name1 ^. theUnique
        , "is attempted to be referenced"
        ]

instance
        ( Pretty (SomeTypeIn uni)
        , Closed uni, uni `Everywhere` PrettyConst
        , Pretty fun
        , Pretty ann
        ) => PrettyBy PrettyConfigPlc (Error uni fun ann) where
    prettyBy _      (ParseErrorE e)           = pretty e
    prettyBy _      (UniqueCoherencyErrorE e) = pretty e
    prettyBy config (TypeErrorE e)            = prettyBy config e
    prettyBy config (NormCheckErrorE e)       = prettyBy config e
    prettyBy _      (FreeVariableErrorE e)    = pretty e

makeClassyPrisms ''ParseError
makeClassyPrisms ''ParserErrorBundle
makeClassyPrisms ''UniqueError
makeClassyPrisms ''NormCheckError
makeClassyPrisms ''TypeError
makeClassyPrisms ''Error

instance AsParserErrorBundle (Error uni fun ann) where
    _ParserErrorBundle = _ParseErrorE

instance AsUniqueError (Error uni fun ann) ann where
    _UniqueError = _UniqueCoherencyErrorE

instance AsTypeError (Error uni fun ann) (Term TyName Name uni fun ()) uni fun ann where
    _TypeError = _TypeErrorE

instance (tyname ~ TyName, name ~ Name) =>
            AsNormCheckError (Error uni fun ann) tyname name uni fun ann where
    _NormCheckError = _NormCheckErrorE

instance AsFreeVariableError (Error uni fun ann) where
    _FreeVariableError = _FreeVariableErrorE
