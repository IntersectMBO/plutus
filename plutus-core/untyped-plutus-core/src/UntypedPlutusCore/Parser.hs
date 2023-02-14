-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}

module UntypedPlutusCore.Parser
    ( parse
    , term
    , program
    , parseTerm
    , parseProgram
    , parseScoped
    , Parser
    , SourcePos
    ) where

import Prelude hiding (fail)

import Control.Monad.Except (MonadError, (<=<))

import PlutusCore qualified as PLC
import PlutusCore.Annotation
import PlutusPrelude (through)
import Text.Megaparsec hiding (ParseError, State, parse)
import UntypedPlutusCore.Check.Uniques (checkProgram)
import UntypedPlutusCore.Core.Type qualified as UPLC
import UntypedPlutusCore.Rename (Rename (rename))

import Data.Text (Text)
import PlutusCore.Error (AsParserErrorBundle)
import PlutusCore.MkPlc (mkIterApp)
import PlutusCore.Parser hiding (parseProgram, parseTerm, program)

-- Parsers for UPLC terms

-- | A parsable UPLC term.
type PTerm = UPLC.Term PLC.Name PLC.DefaultUni PLC.DefaultFun SrcSpan

conTerm :: Parser PTerm
conTerm = withSpan $ \sp ->
    inParens $ UPLC.Constant sp <$> (symbol "con" *> constant)

builtinTerm :: Parser PTerm
builtinTerm = withSpan $ \sp ->
    inParens $ UPLC.Builtin sp <$> (symbol "builtin" *> builtinFunction)

varTerm :: Parser PTerm
varTerm = withSpan $ \sp ->
    UPLC.Var sp <$> name

lamTerm :: Parser PTerm
lamTerm = withSpan $ \sp ->
    inParens $ UPLC.LamAbs sp <$> (symbol "lam" *> trailingWhitespace name) <*> term

appTerm :: Parser PTerm
appTerm = withSpan $ \sp ->
    inBrackets $ mkIterApp sp <$> term <*> some term

delayTerm :: Parser PTerm
delayTerm = withSpan $ \sp ->
    inParens $ UPLC.Delay sp <$> (symbol "delay" *> term)

forceTerm :: Parser PTerm
forceTerm = withSpan $ \sp ->
    inParens $ UPLC.Force sp <$> (symbol "force" *> term)

errorTerm :: Parser PTerm
errorTerm = withSpan $ \sp ->
    inParens $ UPLC.Error sp <$ symbol "error"

-- | Parser for all UPLC terms.
term :: Parser PTerm
term = leadingWhitespace go
  where
    go =
        choice $ map try [
            conTerm
            , builtinTerm
            , varTerm
            , lamTerm
            , appTerm
            , delayTerm
            , forceTerm
            , errorTerm
            ]

-- | Parser for UPLC programs.
program :: Parser (UPLC.Program PLC.Name PLC.DefaultUni PLC.DefaultFun SrcSpan)
program = leadingWhitespace go
  where
    go = do
        prog <- withSpan $ \sp ->
            inParens $ UPLC.Program sp <$> (symbol "program" *> version) <*> term
        notFollowedBy anySingle
        pure prog

-- | Parse a UPLC term. The resulting program will have fresh names. The underlying monad must be capable
-- of handling any parse errors.
parseTerm :: (AsParserErrorBundle e, MonadError e m, PLC.MonadQuote m) => Text -> m PTerm
parseTerm = parseGen term

-- | Parse a UPLC program. The resulting program will have fresh names. The
-- underlying monad must be capable of handling any parse errors.  This passes
-- "test" to the parser as the name of the input stream; to supply a name
-- explicity, use `parse program <name> <input>`.`
parseProgram ::
    (AsParserErrorBundle e, MonadError e m, PLC.MonadQuote m)
    => Text
    -> m (UPLC.Program PLC.Name PLC.DefaultUni PLC.DefaultFun SrcSpan)
parseProgram = parseGen program

-- | Parse and rewrite so that names are globally unique, not just unique within
-- their scope.
parseScoped ::
    (AsParserErrorBundle e, PLC.AsUniqueError e SrcSpan, MonadError e m, PLC.MonadQuote m)
    => Text
    -> m (UPLC.Program PLC.Name PLC.DefaultUni PLC.DefaultFun SrcSpan)
-- don't require there to be no free variables at this point, we might be parsing an open term
parseScoped = through (checkProgram (const True)) <=< rename <=< parseProgram
