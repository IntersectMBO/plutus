{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

-- | Parsers for PLC terms in DefaultUni.
module PlutusCore.Parser
  ( module Export
  , program
  , parseProgram
  , parseTerm
  , parseType
  , SourcePos
  , ParserError (..)
  ) where

import PlutusCore.Annotation
import PlutusCore.Core (Program (..), Term (..), Type)
import PlutusCore.Default
import PlutusCore.Error (ParserError (..), ParserErrorBundle)
import PlutusCore.MkPlc (mkIterApp, mkIterInst)
import PlutusCore.Name.Unique (Name, TyName)
import PlutusCore.Parser.Builtin as Export
import PlutusCore.Parser.ParserCommon as Export
import PlutusCore.Parser.Type as Export
import PlutusCore.Quote (MonadQuote)
import PlutusCore.Version

import Control.Monad (when)
import Control.Monad.Except (MonadError)
import Data.Text (Text)
import Data.Word (Word64)

import Text.Megaparsec (MonadParsec (notFollowedBy), anySingle, choice, many, some, try)
import Text.Megaparsec.Char.Lexer qualified as Lex

-- | A parsable PLC term.
type PTerm = Term TyName Name DefaultUni DefaultFun SrcSpan

varTerm :: Parser PTerm
varTerm = withSpan $ \sp ->
  Var sp <$> name

tyAbsTerm :: Parser PTerm
tyAbsTerm = withSpan $ \sp ->
  inParens $ TyAbs sp <$> (symbol "abs" *> trailingWhitespace tyName) <*> kind <*> term

lamTerm :: Parser PTerm
lamTerm = withSpan $ \sp ->
  inParens $ LamAbs sp <$> (symbol "lam" *> trailingWhitespace name) <*> pType <*> term

appTerm :: Parser PTerm
appTerm = withSpan $ \sp ->
  -- TODO: should not use the same `sp` for all arguments.
  inBrackets $ mkIterApp <$> term <*> (fmap (sp,) <$> some term)

conTerm :: Parser PTerm
conTerm = withSpan $ \sp ->
  inParens $ Constant sp <$> (symbol "con" *> constant)

builtinTerm :: Parser PTerm
builtinTerm = withSpan $ \sp ->
  inParens $ Builtin sp <$> (symbol "builtin" *> builtinFunction)

tyInstTerm :: Parser PTerm
tyInstTerm = withSpan $ \sp ->
  -- TODO: should not use the same `sp` for all arguments.
  inBraces $ mkIterInst <$> term <*> (fmap (sp,) <$> many pType)

unwrapTerm :: Parser PTerm
unwrapTerm = withSpan $ \sp ->
  inParens $ Unwrap sp <$> (symbol "unwrap" *> term)

iwrapTerm :: Parser PTerm
iwrapTerm = withSpan $ \sp ->
  inParens $ IWrap sp <$> (symbol "iwrap" *> pType) <*> pType <*> term

errorTerm :: Parser PTerm
errorTerm = withSpan $ \sp ->
  inParens $ Error sp <$> (symbol "error" *> pType)

constrTerm :: Parser PTerm
constrTerm = withSpan $ \sp ->
  inParens $ do
    let maxTag = fromIntegral (maxBound :: Word64)
    ty <- symbol "constr" *> pType
    tag :: Integer <- lexeme Lex.decimal
    args <- many term
    whenVersion (\v -> v < plcVersion110) $ fail "'constr' is not allowed before version 1.1.0"
    when (tag > maxTag) $ fail "constr tag too large: must be a legal Word64 value"
    pure $ Constr sp ty (fromIntegral tag) args

caseTerm :: Parser PTerm
caseTerm = withSpan $ \sp ->
  inParens $ do
    res <- Case sp <$> (symbol "case" *> pType) <*> term <*> many term
    whenVersion (\v -> v < plcVersion110) $ fail "'case' is not allowed before version 1.1.0"
    pure res

-- | Parser for all PLC terms.
term :: Parser PTerm
term = leadingWhitespace go
  where
    go =
      choice $
        map
          try
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
          , constrTerm
          , caseTerm
          ]

{-| Parse a PLC program. The resulting program will have fresh names. The
underlying monad must be capable of handling any parse errors.  This passes
"test" to the parser as the name of the input stream; to supply a name
explicity, use `parse program <name> <input>`. -}
parseProgram
  :: (MonadError ParserErrorBundle m, MonadQuote m)
  => Text
  -> m (Program TyName Name DefaultUni DefaultFun SrcSpan)
parseProgram = parseGen program

-- | Parser for PLC programs.
program :: Parser (Program TyName Name DefaultUni DefaultFun SrcSpan)
program = leadingWhitespace go
  where
    go = do
      prog <- withSpan $ \sp -> inParens $ do
        v <- symbol "program" *> version
        withVersion v $ Program sp v <$> term
      notFollowedBy anySingle
      pure prog

{-| Parse a PLC term. The resulting program will have fresh names. The underlying monad
must be capable of handling any parse errors. -}
parseTerm
  :: (MonadError ParserErrorBundle m, MonadQuote m)
  => Text -> m (Term TyName Name DefaultUni DefaultFun SrcSpan)
parseTerm = parseGen term

{-| Parse a PLC type. The resulting program will have fresh names. The underlying monad
must be capable of handling any parse errors. -}
parseType
  :: (MonadError ParserErrorBundle m, MonadQuote m)
  => Text -> m (Type TyName DefaultUni SrcSpan)
parseType = parseGen pType
