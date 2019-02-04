{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Language.PlutusIR.Parser where

import           Prelude                      hiding (fail)

import           Control.Applicative          hiding (many, some)
import           Control.Monad.State          hiding (fail)

import qualified Language.PlutusCore          as PLC
import qualified Language.PlutusCore.Constant as PLC
import           Language.PlutusIR            as PIR
import           PlutusPrelude                (prettyString)
import           Text.Megaparsec              hiding (ParseError, State, parse)
import qualified Text.Megaparsec              as Parsec

import           Data.ByteString.Internal     (c2w)
import qualified Data.ByteString.Lazy         as BS
import           Data.Char
import           Data.Foldable
import qualified Data.Map                     as M
import qualified Data.Text                    as T
import           Data.Word
import           GHC.Natural

import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer   as Lex

newtype ParserState = ParserState { identifiers :: M.Map T.Text PLC.Unique }
    deriving (Show)

data ParseError = Overflow Natural Integer
                | UnexpectedKeyword String
                | InternalError String
                deriving (Eq, Ord, Show)

instance ShowErrorComponent ParseError where
    showErrorComponent (Overflow sz i) = "Integer overflow: " ++ show i ++ " does not fit in " ++ show sz ++ " bytes"
    showErrorComponent (UnexpectedKeyword kw) = "Keyword " ++ kw ++ " used as identifier"
    showErrorComponent (InternalError cause) = "Internal error: " ++ cause

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

type Parser = ParsecT ParseError String (StateT ParserState PLC.Quote)
instance (Stream s, PLC.MonadQuote m) => PLC.MonadQuote (ParsecT e s m)

parse :: Parser a -> String -> String -> Either (Parsec.ParseError Char ParseError) a
parse p file str = PLC.runQuote $ flip evalStateT initial $ runParserT p file str

whitespace :: Parser ()
whitespace = Lex.space space1 (Lex.skipLineComment "--") (Lex.skipBlockCommentNested "{-" "-}")

-- Tokens
-- TODO: move this to separate module?

lexeme :: Parser a -> Parser a
lexeme = Lex.lexeme whitespace

symbol :: String -> Parser (Tokens String)
symbol = Lex.symbol whitespace

lparen :: Parser String
lparen = symbol "("
rparen :: Parser String
rparen = symbol ")"

lbracket :: Parser String
lbracket = symbol "["
rbracket :: Parser String
rbracket = symbol "]"

lbrace :: Parser String
lbrace = symbol "{"
rbrace :: Parser String
rbrace = symbol "}"

inParens :: Parser a -> Parser a
inParens = between lparen rparen

inBrackets :: Parser a -> Parser a
inBrackets = between lbracket rbracket

inBraces :: Parser a -> Parser a
inBraces = between lbrace rbrace

reservedWords :: [String]
reservedWords =
    map prettyString PLC.allBuiltinNames ++
    [ "abs"
    , "lam"
    , "ifix"
    , "fun"
    , "all"
    , "bytestring"
    , "integer"
    , "size"
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
    , "termbind"
    , "typebind"
    , "datatypebind"
    , "datatype"
    ]

isIdentifierChar :: Char -> Bool
isIdentifierChar c = isAlphaNum c || c == '_' || c == '\''

reservedWord :: String -> Parser SourcePos
reservedWord w = lexeme $ try $ do
    p <- getPosition
    void $ string w
    notFollowedBy (satisfy isIdentifierChar)
    return p

builtinName :: Parser PLC.BuiltinName
builtinName = lexeme $ choice $ map parseBuiltinName PLC.allBuiltinNames
    where parseBuiltinName :: PLC.BuiltinName -> Parser PLC.BuiltinName
          parseBuiltinName builtin = try $ string (prettyString builtin) >> pure builtin

name :: Parser (Name SourcePos)
name = lexeme $ try $ do
    pos <- getPosition
    void $ lookAhead letterChar
    str <- takeWhileP (Just "identifier") isIdentifierChar
    let word = T.pack str
    if str `elem` reservedWords
        then customFailure $ UnexpectedKeyword $ show word
        else Name pos word <$> intern word

var :: Parser (Name SourcePos)
var = name
tyVar :: Parser (TyName SourcePos)
tyVar = TyName <$> name
builtinVar :: Parser (PLC.Builtin SourcePos)
builtinVar = PLC.BuiltinName <$> getPosition <*> builtinName

-- This should not accept spaces after the sign, hence the `return ()`
integer :: Parser Integer
integer = lexeme $ Lex.signed (return ()) Lex.decimal

natural :: Parser Natural
natural = lexeme Lex.decimal

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

size :: Parser Natural
size = lexeme $ do
    i <- Lex.decimal
    option () $ void $ reservedWord "bytes"
    return i

version :: Parser (PLC.Version SourcePos)
version = lexeme $ do
    p <- getPosition
    x <- Lex.decimal
    void $ char '.'
    y <- Lex.decimal
    void $ char '.'
    PLC.Version p x y <$> Lex.decimal

handleInteger :: SourcePos -> Natural -> Integer -> Parser (PLC.Constant SourcePos)
handleInteger pos s i = case PLC.makeBuiltinInt s i of
    Nothing -> customFailure $ Overflow s i
    Just bi -> pure $ pos <$ bi

constant :: Parser (PLC.Constant SourcePos)
constant = do
    p <- getPosition
    s <- size
    (char '!' >> whitespace >> (handleInteger p s =<< integer) <|> (PLC.BuiltinBS p s <$> bytestring))
        <|> (notFollowedBy (char '!') >> (pure $ PLC.BuiltinSize p s))

recursivity :: Parser Recursivity
recursivity = inParens $ (reservedWord "rec" >> return Rec) <|> (reservedWord "nonrec" >> return NonRec)

funType :: Parser (Type TyName SourcePos)
funType = TyFun <$> reservedWord "fun" <*> typ <*> typ

allType :: Parser (Type TyName SourcePos)
allType = TyForall <$> reservedWord "all" <*> tyVar <*> kind <*> typ

lamType :: Parser (Type TyName SourcePos)
lamType = TyLam <$> reservedWord "lam" <*> tyVar <*> kind <*> typ

ifixType :: Parser (Type TyName SourcePos)
ifixType = TyIFix <$> reservedWord "ifix" <*> typ <*> typ

conType :: Parser (Type TyName SourcePos)
conType = reservedWord "con" >> builtinType

builtinType :: Parser (Type TyName SourcePos)
builtinType = TyBuiltin <$> reservedWord "size" <*> return PLC.TySize
    <|> TyBuiltin <$> reservedWord "integer" <*> return PLC.TyInteger
    <|> TyBuiltin <$> reservedWord "bytestring" <*> return PLC.TyByteString
    <|> TyInt <$> getPosition <*> natural

appType :: Parser (Type TyName SourcePos)
appType = do
    pos  <- getPosition
    fn   <- typ
    args <- some typ
    pure $ foldl' (TyApp pos) fn args

kind :: Parser (Kind SourcePos)
kind = inParens (typeKind <|> sizeKind <|> funKind)
    where
        typeKind = Type <$> reservedWord "type"
        sizeKind = Size <$> reservedWord "size"
        funKind  = KindArrow <$> reservedWord "fun" <*> kind <*> kind

typ :: Parser (Type TyName SourcePos)
typ = (tyVar >>= (\n -> return $ TyVar (nameAttribute $ unTyName n) n))
    <|> (inParens $ funType <|> allType <|> lamType <|> ifixType <|> conType)
    <|> inBrackets appType

varDecl :: Parser (VarDecl TyName Name SourcePos)
varDecl = inParens $ VarDecl <$> reservedWord "vardecl" <*> var <*> typ

tyVarDecl :: Parser (TyVarDecl TyName SourcePos)
tyVarDecl = inParens $ TyVarDecl <$> reservedWord "tyvardecl" <*> tyVar <*> kind

datatype :: Parser (Datatype TyName Name SourcePos)
datatype = inParens $ Datatype <$> reservedWord "datatype"
    <*> tyVarDecl
    <*> some tyVarDecl
    <*> var
    <*> some varDecl

binding :: Parser (Binding TyName Name SourcePos)
binding =  inParens $
    (try $ reservedWord "termbind" >> TermBind <$> getPosition <*> varDecl <*> term)
    <|> (reservedWord "typebind" >> TypeBind <$> getPosition <*> tyVarDecl <*> typ)
    <|> (reservedWord "datatypebind" >> DatatypeBind <$> getPosition <*> datatype)

absTerm :: Parser (Term TyName Name SourcePos)
absTerm = TyAbs <$> reservedWord "abs" <*> tyVar <*> kind <*> term

lamTerm :: Parser (Term TyName Name SourcePos)
lamTerm = LamAbs <$> reservedWord "lam" <*> name <*> typ <*> term

conTerm :: Parser (Term TyName Name SourcePos)
conTerm = Constant <$> reservedWord "con" <*> constant

iwrapTerm :: Parser (Term TyName Name SourcePos)
iwrapTerm = IWrap <$> reservedWord "iwrap" <*> typ <*> typ <*> term

builtinTerm :: Parser (Term TyName Name SourcePos)
builtinTerm = Builtin <$> reservedWord "builtin" <*> builtinVar

unwrapTerm :: Parser (Term TyName Name SourcePos)
unwrapTerm = Unwrap <$> reservedWord "unwrap" <*> term

errorTerm :: Parser (Term TyName Name SourcePos)
errorTerm = Error <$> reservedWord "error" <*> typ

letTerm :: Parser (Term TyName Name SourcePos)
letTerm = Let <$> reservedWord "let" <*> recursivity <*> some (try binding) <*> term

appTerm :: Parser (Term TyName Name SourcePos)
appTerm = do
    pos  <- getPosition
    fn   <- term
    args <- some term
    pure $ foldl' (Apply pos) fn args

tyInstTerm :: Parser (Term TyName Name SourcePos)
tyInstTerm = do
    pos  <- getPosition
    fn   <- term
    args <- some typ
    pure $ foldl' (TyInst pos) fn args

term :: Parser (Term TyName Name SourcePos)
term = (var >>= (\n -> return $ Var (nameAttribute n) n))
    <|> (inParens $ absTerm <|> lamTerm <|> conTerm <|> iwrapTerm <|> builtinTerm <|> unwrapTerm <|> errorTerm <|> letTerm)
    <|> inBraces tyInstTerm
    <|> inBrackets appTerm

-- Note that PIR programs do not actually carry a version number
-- we (optionally) parse it all the same so we can parse all PLC code
program :: Parser (Program TyName Name SourcePos)
program = whitespace >> do
    prog <- inParens $ do
        p <- reservedWord "program"
        option () $ void version
        Program p <$> term
    notFollowedBy anyChar
    return prog
