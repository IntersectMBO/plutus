{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeApplications  #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Language.PlutusIR.Parser
    ( topSourcePos
    , parse
    , parseQuoted
    , term
    , typ
    , program
    , plcTerm
    , plcProgram
    , Parser
    , ParseError (..)
    , Error
    , SourcePos
    ) where

import           Prelude                            hiding (fail)

import           Control.Applicative                hiding (many, some)
import           Control.Monad.State                hiding (fail)

import qualified Language.PlutusCore                as PLC
import qualified Language.PlutusCore.MkPlc          as PLC
import           Language.PlutusIR                  as PIR
import qualified Language.PlutusIR.MkPir            as PIR
import           PlutusPrelude                      (Pretty, display)
import           Text.Megaparsec                    hiding (ParseError, State, parse)
import qualified Text.Megaparsec                    as Parsec

import qualified Data.ByteString                    as BS
import           Data.ByteString.Internal           (c2w)
import           Data.Char
import           Data.Foldable
import qualified Data.Map                           as M
import qualified Data.Text                          as T
import           Data.Word

import qualified Control.Monad.Combinators.NonEmpty as NE
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer         as Lex




newtype ParserState = ParserState { identifiers :: M.Map T.Text PLC.Unique }
    deriving (Show)

data ParseError = UnexpectedKeyword String
                | InternalError String
                deriving (Eq, Ord, Show)

type Error = Parsec.ParseError Char ParseError

instance ShowErrorComponent ParseError where
    showErrorComponent (UnexpectedKeyword kw) = "Keyword " ++ kw ++ " used as identifier"
    showErrorComponent (InternalError cause)  = "Internal error: " ++ cause

topSourcePos :: SourcePos
topSourcePos = initialPos "top"

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

type Parser = ParsecT ParseError T.Text (StateT ParserState PLC.Quote)
instance (Stream s, PLC.MonadQuote m) => PLC.MonadQuote (ParsecT e s m)

parse :: Parser a -> String -> T.Text -> Either (ParseErrorBundle T.Text ParseError) a
parse p file str = PLC.runQuote $ parseQuoted p file str

parseQuoted :: Parser a -> String -> T.Text -> PLC.Quote (Either (ParseErrorBundle T.Text ParseError) a)
parseQuoted p file str = flip evalStateT initial $ runParserT p file str

whitespace :: Parser ()
whitespace = Lex.space space1 (Lex.skipLineComment "--") (Lex.skipBlockCommentNested "{-" "-}")

-- Tokens
-- TODO: move this to separate module?

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

reservedWords :: [T.Text]
reservedWords =
    [ "abs"
    , "lam"
    , "ifix"
    , "fun"
    , "all"
    , "bytestring"
    , "integer"
    , "type"
    , "program"
    , "con"
    , "iwrap"
    , "builtin"
    , "unwrap"
    , "error"
    -- pir-exclusive reserved words
    , "vardecl"
    , "typedecl"
    , "let"
    , "nonrec"
    , "rec"
    , "nonstrict"
    , "strict"
    , "termbind"
    , "typebind"
    , "datatypebind"
    , "datatype"
    ]

isIdentifierChar :: Char -> Bool
isIdentifierChar c = isAlphaNum c || c == '_' || c == '\''

reservedWord :: T.Text -> Parser SourcePos
reservedWord w = lexeme $ try $ do
    p <- getSourcePos
    void $ string w
    notFollowedBy (satisfy isIdentifierChar)
    return p

builtinFunction :: (Bounded fun, Enum fun, Pretty fun) => Parser fun
builtinFunction = lexeme $ choice $ map parseBuiltin [minBound .. maxBound]
    where parseBuiltin builtin = try $ string (display builtin) >> pure builtin

name :: Parser Name
name = lexeme $ try $ do
    void $ lookAhead letterChar
    str <- takeWhileP (Just "identifier") isIdentifierChar
    if str `elem` reservedWords
        then customFailure $ UnexpectedKeyword $ show str
        else Name str <$> intern str

var :: Parser Name
var = name

tyVar :: Parser TyName
tyVar = TyName <$> name

-- This should not accept spaces after the sign, hence the `return ()`
integer :: Parser Integer
integer = lexeme $ Lex.signed (return ()) Lex.decimal

hexChar :: Parser Char
hexChar = toLower <$> oneOf (['0' .. '9'] ++ ['a' .. 'f'] ++ ['A' .. 'F'])

hexPair :: Parser Word8
hexPair = do
    c1 <- hexChar
    c2 <- hexChar
    (+) <$> hexValue c2 <*> ((16 *) <$> hexValue c1)
    where hexValue c
              | isDigit c = pure $ c2w c - c2w '0'
              | c >= 'a' && c <= 'f' = pure $ 10 + (c2w c - c2w 'a')
              | otherwise = customFailure $ InternalError "non-hexadecimal character in bytestring literal"

bytestring :: Parser BS.ByteString
bytestring = lexeme $ BS.pack <$> (char '#' >> many hexPair)

version :: Parser (PLC.Version SourcePos)
version = lexeme $ do
    p <- getSourcePos
    x <- Lex.decimal
    void $ char '.'
    y <- Lex.decimal
    void $ char '.'
    PLC.Version p x y <$> Lex.decimal

constant :: Parser (PLC.Some (PLC.ValueOf PLC.DefaultUni))
constant =
    (reservedWord "integer" >> PLC.someValue <$> integer) <|> (reservedWord "bytestring" >> PLC.someValue <$> bytestring)

recursivity :: Parser Recursivity
recursivity = inParens $ (reservedWord "rec" >> return Rec) <|> (reservedWord "nonrec" >> return NonRec)

strictness :: Parser Strictness
strictness = inParens $ (reservedWord "strict" >> return Strict) <|> (reservedWord "nonstrict" >> return NonStrict)

funType :: Parser (Type TyName PLC.DefaultUni SourcePos)
funType = TyFun <$> reservedWord "fun" <*> typ <*> typ

allType :: Parser (Type TyName PLC.DefaultUni SourcePos)
allType = TyForall <$> reservedWord "all" <*> tyVar <*> kind <*> typ

lamType :: Parser (Type TyName PLC.DefaultUni SourcePos)
lamType = TyLam <$> reservedWord "lam" <*> tyVar <*> kind <*> typ

ifixType :: Parser (Type TyName PLC.DefaultUni SourcePos)
ifixType = TyIFix <$> reservedWord "ifix" <*> typ <*> typ

conType :: Parser (Type TyName PLC.DefaultUni SourcePos)
conType = reservedWord "con" >> builtinType

builtinType :: Parser (Type TyName PLC.DefaultUni SourcePos)
builtinType = do
    p <- getSourcePos
    PLC.mkTyBuiltin @Integer p <$ reservedWord "integer" <|>
        PLC.mkTyBuiltin @BS.ByteString p <$ reservedWord "bytestring"

appType :: Parser (Type TyName PLC.DefaultUni SourcePos)
appType = do
    pos  <- getSourcePos
    fn   <- typ
    args <- some typ
    pure $ foldl' (TyApp pos) fn args

kind :: Parser (Kind SourcePos)
kind = inParens (typeKind <|> funKind)
    where
        typeKind = Type <$> reservedWord "type"
        funKind  = KindArrow <$> reservedWord "fun" <*> kind <*> kind

typ :: Parser (Type TyName PLC.DefaultUni SourcePos)
typ = (tyVar >>= (\n -> getSourcePos >>= \p -> return $ TyVar p n))
    <|> (inParens $ funType <|> allType <|> lamType <|> ifixType <|> conType)
    <|> inBrackets appType

varDecl :: Parser (VarDecl TyName Name PLC.DefaultUni PLC.DefaultFun SourcePos)
varDecl = inParens $ VarDecl <$> reservedWord "vardecl" <*> var <*> typ

tyVarDecl :: Parser (TyVarDecl TyName SourcePos)
tyVarDecl = inParens $ TyVarDecl <$> reservedWord "tyvardecl" <*> tyVar <*> kind

datatype :: Parser (Datatype TyName Name PLC.DefaultUni PLC.DefaultFun SourcePos)
datatype = inParens $ Datatype <$> reservedWord "datatype"
    <*> tyVarDecl
    <*> many tyVarDecl
    <*> var
    <*> many varDecl

binding :: Parser (Binding TyName Name PLC.DefaultUni PLC.DefaultFun SourcePos)
binding =  inParens $
    (try $ reservedWord "termbind" >> TermBind <$> getSourcePos <*> strictness <*> varDecl <*> term)
    <|> (reservedWord "typebind" >> TypeBind <$> getSourcePos <*> tyVarDecl <*> typ)
    <|> (reservedWord "datatypebind" >> DatatypeBind <$> getSourcePos <*> datatype)

-- A small type wrapper for parsers that are parametric in the type of term they parse
type Parametric = forall term. PIR.TermLike term TyName Name PLC.DefaultUni PLC.DefaultFun => Parser (term SourcePos) -> Parser (term SourcePos)

absTerm :: Parametric
absTerm tm = PIR.tyAbs <$> reservedWord "abs" <*> tyVar <*> kind <*> tm

lamTerm :: Parametric
lamTerm tm = PIR.lamAbs <$> reservedWord "lam" <*> name <*> typ <*> tm

conTerm :: Parametric
conTerm _tm = PIR.constant <$> reservedWord "con" <*> constant

iwrapTerm :: Parametric
iwrapTerm tm = PIR.iWrap <$> reservedWord "iwrap" <*> typ <*> typ <*> tm

builtinTerm :: Parametric
builtinTerm _term = PIR.builtin <$> reservedWord "builtin" <*> builtinFunction

unwrapTerm :: Parametric
unwrapTerm tm = PIR.unwrap <$> reservedWord "unwrap" <*> tm

errorTerm :: Parametric
errorTerm _tm = PIR.error <$> reservedWord "error" <*> typ

letTerm :: Parser (Term TyName Name PLC.DefaultUni PLC.DefaultFun SourcePos)
letTerm = Let <$> reservedWord "let" <*> recursivity <*> NE.some (try binding) <*> term

appTerm :: Parametric
appTerm tm = PIR.mkIterApp <$> getSourcePos <*> tm <*> some tm

tyInstTerm :: Parametric
tyInstTerm tm = PIR.mkIterInst <$> getSourcePos <*> tm <*> some typ

term' :: Parametric
term' other = (var >>= (\n -> getSourcePos >>= \p -> return $ PIR.var p n))
    <|> (inParens $ absTerm self <|> lamTerm self <|> conTerm self <|> iwrapTerm self <|> builtinTerm self <|> unwrapTerm self <|> errorTerm self <|> other)
    <|> inBraces (tyInstTerm self)
    <|> inBrackets (appTerm self)
    where self = term' other

term :: Parser (Term TyName Name PLC.DefaultUni PLC.DefaultFun SourcePos)
term = term' letTerm

plcTerm :: Parser (PLC.Term TyName Name PLC.DefaultUni PLC.DefaultFun SourcePos)
plcTerm = term' empty

-- Note that PIR programs do not actually carry a version number
-- we (optionally) parse it all the same so we can parse all PLC code
program :: Parser (Program TyName Name PLC.DefaultUni PLC.DefaultFun SourcePos)
program = whitespace >> do
    prog <- inParens $ do
        p <- reservedWord "program"
        option () $ void version
        Program p <$> term
    notFollowedBy anySingle
    return prog

plcProgram :: Parser (PLC.Program TyName Name PLC.DefaultUni PLC.DefaultFun SourcePos)
plcProgram = whitespace >> do
    prog <- inParens $ PLC.Program <$> reservedWord "program" <*> version <*> plcTerm
    notFollowedBy anySingle
    return prog
