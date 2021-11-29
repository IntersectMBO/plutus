-- editorconfig-checker-disable-file
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module PlutusCore.Parser.Type where

import PlutusPrelude

import PlutusCore.Core.Type
import PlutusCore.Data
import PlutusCore.Default
import PlutusCore.MkPlc (mkIterTyApp)
import PlutusCore.Name
import PlutusCore.Parser.ParserCommon

import Control.Monad
import Data.ByteString (ByteString)
import Data.Text (Text)
import Text.Megaparsec hiding (ParseError, State, many, parse, some)

-- | A PLC @Type@ to be parsed. ATM the parser only works
-- for types in the @DefaultUni@ with @DefaultFun@.
type PType = Type TyName DefaultUni SourcePos

varType :: Parser PType
varType = TyVar <$> getSourcePos <*> tyName

funType :: Parser PType
funType = inParens $ TyFun <$> wordPos "fun" <*> pType <*> pType

allType :: Parser PType
allType = inParens $ TyForall <$> wordPos "all" <*> tyName <*> kind <*> pType

lamType :: Parser PType
lamType = inParens $ TyLam <$> wordPos "lam" <*> tyName <*> kind <*> pType

ifixType :: Parser PType
ifixType = inParens $ TyIFix <$> wordPos "ifix" <*> pType <*> pType

builtinType :: Parser PType
builtinType = inParens $ do
    ann <- wordPos "con"
    SomeTypeIn (Kinded uni) <- defaultUni
    pure . TyBuiltin ann $ SomeTypeIn uni

prodType :: Parser PType
prodType = inParens $ TyProd <$> wordPos "prod" <*> many pType

sumType :: Parser PType
sumType = inParens $ TySum <$> wordPos "sum" <*> many pType

appType :: Parser PType
appType = inBrackets $ do
    pos  <- getSourcePos
    fn   <- pType
    args <- some pType
    pure $ mkIterTyApp pos fn args

kind :: Parser (Kind SourcePos)
kind = inParens (typeKind <|> funKind)
    where
        typeKind = Type <$> wordPos "type"
        funKind  = KindArrow <$> wordPos "fun" <*> kind <*> kind

-- | Parser for @PType@.
pType :: Parser PType
pType = choice $ map try
    [ funType
    , ifixType
    , allType
    , builtinType
    , lamType
    , appType
    , varType
    , prodType
    , sumType
    ]

-- | Parser for built-in type applications.
defaultUniApplication :: Parser (SomeTypeIn (Kinded DefaultUni))
defaultUniApplication = do
    -- Parse the head of the application.
    f <- defaultUni
    -- Parse the arguments.
    as <- many defaultUni
    -- Iteratively apply the head to the arguments checking that the kinds match and
    -- failing otherwise.
    foldM tryUniApply f as

-- | Parser for built-in types (the ones from 'DefaultUni' specifically).
--
-- 'Kinded' is needed for checking that a type function can be applied to its argument.
-- I.e. we do Plutus kind checking of builtin type applications during parsing, which is
-- unfortunate, but there's no way we could construct a 'DefaultUni' otherwise.
--
-- In case of kind error no sensible message is shown, only an overly general one:
--
-- >>> :set -XTypeApplications
-- >>> :set -XOverloadedStrings
-- >>> import PlutusCore.Error
-- >>> import PlutusCore.Quote
-- >>> let runP = putStrLn . either display display . runQuoteT . parseGen @ParserErrorBundle defaultUni
-- >>> runP "(list integer)"
-- (list integer)
-- >>> runP "(bool integer)"
-- test:1:14:
--   |
-- 1 | (bool integer)
--   |              ^
-- expecting "bool", "bytestring", "data", "integer", "list", "pair", "string", "unit", or '('
--
-- This is to be fixed.
--
-- One thing we could do to avoid doing kind checking during parsing is to parse into
--
--     data TextualUni a where
--         TextualUni :: TextualUni (Esc (Tree Text))
--
-- i.e. parse into @Tree Text@ and do the kind checking afterwards, but given that we'll still need
-- to do the kind checking of builtins regardless (even for UPLC), we don't win much by deferring
-- doing it.
defaultUni :: Parser (SomeTypeIn (Kinded DefaultUni))
defaultUni = choice $ map try
    [ inParens defaultUniApplication
    , someType @_ @Integer <$ symbol "integer"
    , someType @_ @ByteString <$ symbol "bytestring"
    , someType @_ @Text <$ symbol "string"
    , someType @_ @() <$ symbol "unit"
    , someType @_ @Bool <$ symbol "bool"
    , someType @_ @[] <$ symbol "list"
    , someType @_ @(,) <$ symbol "pair"
    , someType @_ @Data <$ symbol "data"
    ]

tyName :: Parser TyName
tyName = TyName <$> name
