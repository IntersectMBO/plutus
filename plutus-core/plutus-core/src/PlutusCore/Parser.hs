{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE OverloadedStrings   #-}


module PlutusCore.Parser
    ( parseProgram
    , parseTerm
    , parseType
    , ParseError(..)
    ) where

import Data.ByteString.Lazy (ByteString)
import Data.Text qualified as T
import PlutusCore.Core (Program (..), Term (..), Type)
import PlutusCore.Default
import PlutusCore.Error (ParseError (..))
import PlutusCore.MkPlc (mkIterApp, mkIterInst)
import PlutusCore.Name (Name, TyName)
import PlutusCore.Parser.ParserCommon
import Text.Megaparsec (MonadParsec (notFollowedBy), SourcePos, anySingle, choice, getSourcePos, many, try)
import Text.Megaparsec.Error (ParseErrorBundle)

-- Parsers for PLC terms

-- | A parsable PLC term.
type PTerm = Term TyName Name DefaultUni DefaultFun SourcePos

varTerm :: Parser PTerm
varTerm = Var <$> getSourcePos <*> name

tyAbsTerm :: Parser PTerm
tyAbsTerm = inParens $ TyAbs <$> wordPos "abs" <*> tyName  <*> kind <*> term

lamTerm :: Parser PTerm
lamTerm = inParens $ LamAbs <$> wordPos "lam" <*> name <*> pType <*> term

appTerm :: Parser PTerm
appTerm = inBrackets $ do
    pos <- getSourcePos
    tm <- term
    tms <- many term
    pure $ mkIterApp pos tm tms

conTerm :: Parser PTerm
conTerm = inParens $ Constant <$> wordPos "con" <*> constant

builtinTerm :: Parser PTerm
builtinTerm = inParens $ Builtin <$> wordPos "builtin" <*> builtinFunction

tyInstTerm :: Parser PTerm
tyInstTerm = inBraces $ do
    pos <- getSourcePos
    tm <- term
    tys <- many pType
    pure $ mkIterInst pos tm tys

unwrapTerm :: Parser PTerm
unwrapTerm = inParens $ Unwrap <$> wordPos "unwrap" <*> term

iwrapTerm :: Parser PTerm
iwrapTerm = inParens $ IWrap <$> wordPos "iwrap" <*> pType <*> pType <*> term

errorTerm
    :: Parser PTerm
errorTerm = inParens $ Error <$> wordPos "error" <*> pType

-- | Parser for all PLC terms.
term :: Parser PTerm
term = choice $ map try
    [ tyAbsTerm
    , lamTerm
    , appTerm
    , conTerm
    , builtinTerm
    , tyInstTerm
    , unwrapTerm
    , iwrapTerm
    , errorTerm
    , varTerm
    ]

-- | Parse a PLC program. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseProgram ::
    ByteString -> Either (ParseErrorBundle T.Text ParseError) (Program TyName Name DefaultUni DefaultFun SourcePos)
parseProgram = parseGen program

-- | Parser for PLC programs.
program :: Parser (Program TyName Name DefaultUni DefaultFun SourcePos)
program = whitespace >> do
    prog <- inParens $ Program <$> wordPos "program" <*> version <*> term
    notFollowedBy anySingle
    return prog

-- | Parse a PLC term. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseTerm ::
    ByteString ->
        Either (ParseErrorBundle T.Text ParseError) (Term TyName Name DefaultUni DefaultFun SourcePos)
parseTerm = parseGen term

-- | Parse a PLC type. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseType ::
    ByteString ->
        Either (ParseErrorBundle T.Text ParseError) (Type TyName DefaultUni SourcePos)
parseType = parseGen pType
