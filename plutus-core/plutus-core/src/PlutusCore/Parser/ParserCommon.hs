{-# LANGUAGE GADTs             #-}
{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -Wno-deferred-out-of-scope-variables #-}

-- | Common functions for parsers of UPLC, PLC, and PIR.

module PlutusCore.Parser.ParserCommon where

import Data.ByteString.Char8 (singleton)
import Data.Char (isAlphaNum)
import Data.Map qualified as M
import Data.Text qualified as T
-- import PlutusCore qualified as PLC hiding (PlutusCore.Parser)
import PlutusPrelude
import Text.Megaparsec hiding (ParseError, State, parse, some)
import Text.Megaparsec.Char (char, letterChar, space1, string)
import Text.Megaparsec.Char.Lexer qualified as Lex

import Control.Monad.State (MonadState (get, put), StateT, evalStateT)

import PlutusCore.Core.Type qualified as PLC
import PlutusCore.Default qualified as PLC
import PlutusCore.Error qualified as PLC
import PlutusCore.Name qualified as PLC
import PlutusCore.Quote qualified as PLC
import Universe.Core (someValue)

newtype ParserState = ParserState { identifiers :: M.Map T.Text PLC.Unique }
    deriving (Show)

type Parser =
    ParsecT PLC.ParseError T.Text (StateT ParserState PLC.Quote)

instance (Stream s, PLC.MonadQuote m) => PLC.MonadQuote (ParsecT e s m)

initial :: ParserState
initial = ParserState M.empty

-- | Return the unique identifier of a name.
-- If it's not in the current parser state, map the name to a fresh id
-- and add it to the state. Used in the Name parser.
intern :: (MonadState ParserState m, PLC.MonadQuote m)
    => T.Text -> m PLC.Unique
intern n = do
    st <- get
    case M.lookup n (identifiers st) of
        Just u -> return u
        Nothing -> do
            fresh <- PLC.freshUnique
            let identifiers' = M.insert n fresh $ identifiers st
            put $ ParserState identifiers'
            return fresh

parse :: Parser a -> String -> T.Text -> Either (ParseErrorBundle T.Text PLC.ParseError) a
parse p file str = PLC.runQuote $ parseQuoted p file str

parseQuoted :: Parser a -> String -> T.Text -> PLC.Quote
                   (Either (ParseErrorBundle T.Text PLC.ParseError) a)
parseQuoted p file str = flip evalStateT initial $ runParserT p file str

-- | Space consumer.
whitespace :: Parser ()
whitespace = Lex.space space1 (Lex.skipLineComment "--") (Lex.skipBlockCommentNested "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = Lex.lexeme whitespace

symbol :: T.Text -> Parser T.Text
symbol = Lex.symbol whitespace

-- | A PLC @Type@ to be parsed. ATM the parser only works
-- for types in the @DefaultUni@ with @DefaultFun@.
type PType = PLC.Type PLC.TyName PLC.DefaultUni SourcePos

varType :: Parser PType
varType = PLC.TyVar <$> getSourcePos <*> tyName

funType :: Parser PType
funType = PLC.TyFun <$> wordPos "fun" <*> pType <*> pType

allType :: Parser PType
allType = PLC.TyForall <$> wordPos "all" <*> tyName <*> kind <*> pType

lamType :: Parser PType
lamType = PLC.TyLam <$> wordPos "lam" <*> tyName <*> kind <*> pType

ifixType :: Parser PType
ifixType = PLC.TyIFix <$> wordPos "ifix" <*> pType <*> pType

builtinType :: Parser PType
builtinType = PLC.TyBuiltin <$> wordPos "con" <*> defaultUniType

appType :: Parser PType
appType = do
    pos  <- getSourcePos
    fn   <- pType
    args <- some pType
    pure $ foldl' (PLC.TyApp pos) fn args

kind :: Parser (PLC.Kind SourcePos)
kind = inParens (typeKind <|> funKind)
    where
        typeKind = PLC.Type <$> wordPos "type"
        funKind  = PLC.KindArrow <$> wordPos "fun" <*> kind <*> kind

-- | Parser for @PType@.
pType :: Parser PType
pType = choice
    [inParens pType
    , varType
    , funType
    , ifixType
    , allType
    , builtinType
    , lamType
    , inBrackets appType
    ]

defaultUniType :: Parser (PLC.SomeTypeIn PLC.DefaultUni)
defaultUniType = choice
  [ inParens defaultUniType
  , PLC.SomeTypeIn PLC.DefaultUniInteger <$ symbol "integer"
  , PLC.SomeTypeIn PLC.DefaultUniByteString <$ symbol "bytestring"
  , PLC.SomeTypeIn PLC.DefaultUniString <$ symbol "symbol"
  , PLC.SomeTypeIn PLC.DefaultUniUnit <$ symbol "unit"
  , PLC.SomeTypeIn PLC.DefaultUniBool <$ symbol "bool"
  , PLC.SomeTypeIn PLC.DefaultUniProtoList <$ symbol "list"
  , PLC.SomeTypeIn PLC.DefaultUniProtoPair <$ symbol "pair"
  -- , PLC.SomeTypeIn DefaultUniApply <$ symbol "?" TODO need to make this an operator
  , PLC.SomeTypeIn PLC.DefaultUniData <$ symbol "data" ]

lbracket :: Parser T.Text
lbracket = symbol "["
rbracket :: Parser T.Text
rbracket = symbol "]"

lbrace :: Parser T.Text
lbrace = symbol "{"
rbrace :: Parser T.Text
rbrace = symbol "}"

inParens :: Parser a -> Parser a
inParens = between (symbol "(") (symbol ")")

inBrackets :: Parser a -> Parser a
inBrackets = between lbracket rbracket

inBraces :: Parser a-> Parser a
inBraces = between lbrace rbrace

isIdentifierChar :: Char -> Bool
isIdentifierChar c = isAlphaNum c || c == '_' || c == '\''

-- | Create a parser that matches the input word and returns its source position.
-- This is for attaching source positions to parsed terms/programs.
-- getSourcePos is not cheap, don't call it on matching of every token.
wordPos ::
    -- | The word to match
    T.Text -> Parser SourcePos
wordPos w = lexeme $ try $ getSourcePos <* symbol w

builtinFunction :: Parser PLC.DefaultFun
builtinFunction = lexeme $ choice $ map parseBuiltin [minBound .. maxBound]
    where parseBuiltin builtin = try $ string (display builtin) >> pure builtin

version :: Parser (PLC.Version SourcePos)
version = lexeme $ do
    p <- getSourcePos
    x <- Lex.decimal
    void $ char '.'
    y <- Lex.decimal
    void $ char '.'
    PLC.Version p x y <$> Lex.decimal

name :: Parser PLC.Name
name = lexeme $ try $ do
    void $ lookAhead letterChar
    str <- takeWhileP (Just "identifier") isIdentifierChar
    PLC.Name str <$> intern str

tyName :: Parser PLC.TyName
tyName = PLC.TyName <$> name

-- | Turn a parser that can succeed without consuming any input into one that fails in this case.
enforce :: Parser a -> Parser a
enforce p = do
    (input, x) <- match p
    guard . not $ T.null input
    pure x

-- | Parser for integer constants.
conInt :: Parser (PLC.Some (PLC.ValueOf PLC.DefaultUni))
conInt = do
    con::Integer <- lexeme Lex.decimal
    pure $ someValue con

-- | Parser for single quoted char.
conChar :: Parser (PLC.Some (PLC.ValueOf PLC.DefaultUni))
conChar = do
    con <- between (char '\'') (char '\'') Lex.charLiteral
    pure $ someValue $ singleton con

-- | Parser for double quoted string.
conText :: Parser (PLC.Some (PLC.ValueOf PLC.DefaultUni))
conText = do
    con <- char '\"' *> manyTill Lex.charLiteral (char '\"')
    pure $ someValue $ T.pack con

-- | Parser for unit.
conUnit :: Parser (PLC.Some (PLC.ValueOf PLC.DefaultUni))
conUnit = someValue () <$ symbol "unit"

-- | Parser for bool.
conBool :: Parser (PLC.Some (PLC.ValueOf PLC.DefaultUni))
conBool = choice
    [ someValue True <$ symbol "True"
    , someValue False <$ symbol "False"
    ]

--TODO fix these (add parsing of constant after symbol?):
-- conPair :: Parser (PLC.Some (PLC.ValueOf PLC.DefaultUni))
-- conPair = someValue (,) <$ symbol "pair"
-- conList :: Parser (PLC.Some (PLC.ValueOf PLC.DefaultUni))
-- conList = someValue [] <$ symbol "list"
-- conData :: Parser (PLC.Some (PLC.ValueOf PLC.DefaultUni))
-- conData = someValue Data? <$ symbol "data"

constant :: Parser (PLC.Some (PLC.ValueOf PLC.DefaultUni))
constant = choice
    [ inParens constant
    , conInt
    , conChar
    , conText
    , conUnit
    , conBool
    -- , conPair
    -- , conList
    -- , conData
    ]

-- | Parser for a constant term. Currently the syntax is "con defaultUniType val".
constantTerm :: Parser (PLC.Term PLC.TyName PLC.Name PLC.DefaultUni PLC.DefaultFun SourcePos)
constantTerm = do
    p <- wordPos "con"
    _conTy <- defaultUniType -- TODO: do case of for each ty?
    con <- constant
    pure $ PLC.Constant p con
