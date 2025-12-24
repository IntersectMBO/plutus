-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

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

import Control.Monad (fail, when, (<=<))
import Control.Monad.Except

import PlutusCore qualified as PLC
import PlutusCore.Annotation
import PlutusCore.Error qualified as PLC
import PlutusPrelude (through)
import Text.Megaparsec hiding (ParseError, State, parse)
import Text.Megaparsec.Char (char)
import Text.Megaparsec.Char.Lexer qualified as Lex
import UntypedPlutusCore.Check.Uniques (checkProgram)
import UntypedPlutusCore.Core.Type qualified as UPLC
import UntypedPlutusCore.Rename (Rename (rename))

import Data.Text (Text)
import Data.Vector qualified as V
import Data.Word (Word64)
import PlutusCore.MkPlc (mkIterApp)
import PlutusCore.Parser hiding (parseProgram, parseTerm, program)
import PlutusCore.Version

-- Parsers for UPLC terms

-- | A parsable UPLC term.
type PTerm = UPLC.Term PLC.Name PLC.DefaultUni PLC.DefaultFun SrcSpan

conTerm :: SrcSpan -> Parser PTerm
conTerm sp =
  UPLC.Constant sp <$> constant

builtinTerm :: SrcSpan -> Parser PTerm
builtinTerm sp =
  UPLC.Builtin sp <$> builtinFunction

varTerm :: Parser PTerm
varTerm =
  withSpan $ \sp -> UPLC.Var sp <$> name

lamTerm :: SrcSpan -> Parser PTerm
lamTerm sp =
  UPLC.LamAbs sp <$> (trailingWhitespace name) <*> term

appTerm :: SrcSpan -> Parser PTerm
appTerm sp =
  -- TODO: should not use the same `sp` for all arguments.
  mkIterApp <$> term <*> (fmap (sp,) <$> some term)

delayTerm :: SrcSpan -> Parser PTerm
delayTerm sp =
  UPLC.Delay sp <$> term

forceTerm :: SrcSpan -> Parser PTerm
forceTerm sp =
  UPLC.Force sp <$> term

errorTerm :: SrcSpan -> Parser PTerm
errorTerm sp =
  return (UPLC.Error sp)

constrTerm :: SrcSpan -> Parser PTerm
constrTerm sp = do
  let maxTag = fromIntegral (maxBound :: Word64)
  tag :: Integer <- lexeme Lex.decimal
  args <- many term
  whenVersion (\v -> v < plcVersion110) $ fail "'constr' is not allowed before version 1.1.0"
  when (tag > maxTag) $ fail "constr tag too large: must be a legal Word64 value"
  pure $ UPLC.Constr sp (fromIntegral tag) args

caseTerm :: SrcSpan -> Parser PTerm
caseTerm sp = do
  res <- UPLC.Case sp <$> term <*> (V.fromList <$> many term)
  whenVersion (\v -> v < plcVersion110) $ fail "'case' is not allowed before version 1.1.0"
  pure res

-- | Parser for all UPLC terms.
term :: Parser PTerm
term =
  leadingWhitespace $ do
    choice
      [ tryAppTerm
      , tryTermInParens
      , varTerm
      ]
  where
    tryAppTerm :: Parser PTerm
    tryAppTerm =
      withSpan $ \sp ->
        between
          (symbol "[" <?> "opening bracket '['")
          (char ']' <?> "closing bracket ']'")
          (appTerm sp)

    tryTermInParens :: Parser PTerm
    tryTermInParens =
      withSpan $ \sp ->
        between
          (symbol "(" <?> "opening parenthesis '('")
          (char ')' <?> "closing parenthesis ')'")
          ( choice
              [ symbol "builtin" *> builtinTerm sp
              , symbol "lam" *> lamTerm sp
              , symbol "constr" *> constrTerm sp -- "constr" must come before "con"
              , symbol "con" *> conTerm sp
              , symbol "delay" *> delayTerm sp
              , symbol "force" *> forceTerm sp
              , symbol "error" *> errorTerm sp
              , symbol "case" *> caseTerm sp
              ]
              <?> "term keyword (builtin, lam, constr, con, delay, force, error, case)"
          )

-- | Parser for UPLC programs.
program :: Parser (UPLC.Program PLC.Name PLC.DefaultUni PLC.DefaultFun SrcSpan)
program = leadingWhitespace go
  where
    go = do
      prog <- withSpan $ \sp -> inParens $ do
        v <- symbol "program" *> version
        withVersion v $ UPLC.Program sp v <$> term
      notFollowedBy anySingle
      pure prog

{-| Parse a UPLC term. The resulting program will have fresh names. The underlying monad must be capable
of handling any parse errors. -}
parseTerm :: (MonadError PLC.ParserErrorBundle m, PLC.MonadQuote m) => Text -> m PTerm
parseTerm = parseGen term

{-| Parse a UPLC program. The resulting program will have fresh names. The
underlying monad must be capable of handling any parse errors.  This passes
"test" to the parser as the name of the input stream; to supply a name
explicity, use `parse program <name> <input>`.` -}
parseProgram
  :: (MonadError PLC.ParserErrorBundle m, PLC.MonadQuote m)
  => Text
  -> m (UPLC.Program PLC.Name PLC.DefaultUni PLC.DefaultFun SrcSpan)
parseProgram = parseGen program

{-| Parse and rewrite so that names are globally unique, not just unique within
their scope. -}
parseScoped
  :: (MonadError (PLC.Error uni fun SrcSpan) m, PLC.MonadQuote m)
  => Text
  -> m (UPLC.Program PLC.Name PLC.DefaultUni PLC.DefaultFun SrcSpan)
-- don't require there to be no free variables at this point, we might be parsing an open term
parseScoped =
  through (modifyError PLC.UniqueCoherencyErrorE . checkProgram (const True))
    <=< rename
    <=< modifyError PLC.ParseErrorE . parseProgram
