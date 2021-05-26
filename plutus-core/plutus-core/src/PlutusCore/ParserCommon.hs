{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

-- | Common functions for parsers of UPLC, PLC, and PIR.
module PlutusCore.ParserCommon where

import           Data.Char                  (isAlphaNum)
import qualified Data.Map                   as M
import qualified Data.Text                  as T
import           ErrorCode                  (ErrorCode (ErrorCode), HasErrorCode (..))
import qualified PlutusCore                 as PLC
import qualified PlutusCore.Parsable        as PLC
import           PlutusPrelude
import           Text.Megaparsec            hiding (ParseError, State, parse)
import qualified Text.Megaparsec            as Parsec
import           Text.Megaparsec.Char       (char, letterChar, space1, string)
import qualified Text.Megaparsec.Char.Lexer as Lex

import           Control.Monad.State        (MonadState (get, put), StateT, evalStateT)

import           Data.Proxy                 (Proxy (Proxy))

data ParseError = UnknownBuiltinType T.Text
                | InvalidConstant T.Text T.Text
                deriving (Eq, Ord, Show)

instance HasErrorCode ParseError where
      errorCode UnknownBuiltinType {} = ErrorCode 5
      errorCode InvalidConstant {}    = ErrorCode 4

type Error = Parsec.ParseError Char ParseError

instance ShowErrorComponent ParseError where
    showErrorComponent (UnknownBuiltinType ty) = "Unknown built-in type: " ++ T.unpack ty
    showErrorComponent (InvalidConstant ty con) =
        "Invalid constant: " ++ T.unpack con ++ " of type " ++ T.unpack ty
newtype ParserState = ParserState { identifiers :: M.Map T.Text PLC.Unique }
    deriving (Show)

initial :: ParserState
initial = ParserState M.empty

intern :: (MonadState ParserState m, PLC.MonadQuote m) => T.Text -> m PLC.Unique
intern n = do
    st <- get
    case M.lookup n (identifiers st) of
        Just u -> return u
        Nothing -> do
            fresh <- PLC.freshUnique
            let identifiers' = M.insert n fresh $ identifiers st
            put $ ParserState identifiers'
            return fresh

parse :: Parser a -> String -> T.Text -> Either (ParseErrorBundle T.Text ParseError) a
parse p file str = PLC.runQuote $ parseQuoted p file str

parseQuoted :: Parser a -> String -> T.Text -> PLC.Quote (Either (ParseErrorBundle T.Text ParseError) a)
parseQuoted p file str = flip evalStateT initial $ runParserT p file str

type Parser = ParsecT ParseError T.Text (StateT ParserState PLC.Quote)
instance (Stream s, PLC.MonadQuote m) => PLC.MonadQuote (ParsecT e s m)

topSourcePos :: SourcePos
topSourcePos = initialPos "top"

whitespace :: Parser ()
whitespace = Lex.space space1 (Lex.skipLineComment "--") (Lex.skipBlockCommentNested "{-" "-}")

lexeme :: Parser a -> Parser a
lexeme = Lex.lexeme whitespace

symbol :: T.Text -> Parser T.Text
symbol = Lex.symbol whitespace

lparen :: Parser T.Text
lparen = symbol "("
rparen :: Parser T.Text
rparen = symbol ")"

lbracket :: Parser T.Text
lbracket = symbol "["
rbracket :: Parser T.Text
rbracket = symbol "]"

lbrace :: Parser T.Text
lbrace = symbol "{"
rbrace :: Parser T.Text
rbrace = symbol "}"

inParens :: Parser a -> Parser a
inParens = between lparen rparen

inBrackets :: Parser a -> Parser a
inBrackets = between lbracket rbracket

inBraces :: Parser a -> Parser a
inBraces = between lbrace rbrace

isIdentifierChar :: Char -> Bool
isIdentifierChar c = isAlphaNum c || c == '_' || c == '\''

reservedWord :: T.Text -> Parser SourcePos
reservedWord w = lexeme $ try $ do
    p <- getSourcePos
    void $ string w
    notFollowedBy (satisfy isIdentifierChar)
    return p

-- | Parse a type tag by feeding the output of 'closedChunk' to 'PLC.parse'.
builtinTypeTag
    :: PLC.Parsable (PLC.Some uni)
    => Parser (PLC.Some uni)
builtinTypeTag = do
    uniText <- closedChunk
    case PLC.parse uniText of
        Nothing  -> customFailure $ UnknownBuiltinType uniText
        Just uni -> pure uni

-- | Parse a constant by parsing a type tag first and using the type-specific parser of constants.
-- Uses 'PLC.parse' under the hood for both types and constants.
constant
    :: (PLC.Parsable (PLC.Some uni), PLC.Closed uni, uni `PLC.Everywhere` PLC.Parsable)
    => Parser (PLC.Some (PLC.ValueOf uni))
constant = do
    -- We use 'match' for remembering the textual representation of the parsed type tag,
    -- so that we can show it in the error message if the constant fails to parse.
    (uniText, PLC.Some uni) <- match builtinTypeTag
    conText <- closedChunk
    case PLC.bring (Proxy @PLC.Parsable) uni $ PLC.parse conText of
        Nothing  -> customFailure $ InvalidConstant uniText conText
        Just con -> pure . PLC.Some $ PLC.ValueOf uni con

builtinFunction :: (Bounded fun, Enum fun, Pretty fun) => Parser fun
builtinFunction = lexeme $ choice $ map parseBuiltin [minBound .. maxBound]
    where parseBuiltin builtin = try $ string (display builtin) >> pure builtin

name :: Parser PLC.Name
name = lexeme $ try $ do
    void $ lookAhead letterChar
    str <- takeWhileP (Just "identifier") isIdentifierChar
    PLC.Name str <$> intern str

var :: Parser PLC.Name
var = name

tyVar :: Parser PLC.TyName
tyVar = PLC.TyName <$> name

version :: Parser (PLC.Version SourcePos)
version = lexeme $ do
    p <- getSourcePos
    x <- Lex.decimal
    void $ char '.'
    y <- Lex.decimal
    void $ char '.'
    PLC.Version p x y <$> Lex.decimal

-- | Turn a parser that can succeed without consuming any input into one that fails in this case.
enforce :: Parser a -> Parser a
enforce p = do
    (input, x) <- match p
    guard . not $ T.null input
    pure x

-- | Consume a chunk of text and either stop on whitespace (and consume it) or on a \')\' (without
-- consuming it). We need this for collecting a @Text@ to pass it to 'PLC.parse' in order to
-- parse a built-in type or a constant. This is neither efficient (because of @manyTill anySingle@),
-- nor future-proof (what if some future built-in type has parens in its syntax?). A good way of
-- resolving this would be to turn 'PLC.parse' into a proper parser rather than just a function
-- from @Text@, but PLC's parser also uses 'PLC.parse' and it's currently not @megaparsec@-based,
-- and so mixing two distinct parsing machines doesn't sound too exciting.
--
-- Note that this also fails on @(con string \"yes (no)\")@ as well as @con unit ()@, so it really
-- should be fixed somehow.
closedChunk :: Parser T.Text
closedChunk = T.pack <$> manyTill anySingle end where
    end = enforce whitespace <|> void (lookAhead $ char ')')
