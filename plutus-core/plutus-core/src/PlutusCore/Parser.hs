{-# LANGUAGE AllowAmbiguousTypes #-}
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
import PlutusCore.Default (DefaultFun, DefaultUni)
import PlutusCore.Error (ParseError (..))
import PlutusCore.Name (Name, TyName)
import PlutusCore.Parser.ParserCommon
import Text.Megaparsec (MonadParsec (notFollowedBy), SourcePos, anySingle, choice, getSourcePos, try)
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
appTerm = inBrackets $ Apply <$> getSourcePos <*> term <*> term

-- | Parser for a constant term. Currently the syntax is "con defaultUniType val".
conTerm :: Parser PTerm
conTerm = inParens $ do
    p <- wordPos "con"
    _conTy <- defaultUniType -- TODO: do case of for each ty?
    con <- constant
    pure $ Constant p con

builtinTerm :: Parser PTerm
builtinTerm = inParens $ do
    p <- wordPos "builtin"
    fn <- builtinFunction
    pure $ Builtin p fn
    -- Builtin <$> wordPos "builtin" <*> builtinFunction

tyInstTerm :: Parser PTerm
tyInstTerm = inBraces $ TyInst <$> getSourcePos <*> term <*> pType

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
