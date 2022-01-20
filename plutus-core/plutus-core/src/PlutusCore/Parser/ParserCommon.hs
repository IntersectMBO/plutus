{-# LANGUAGE GADTs             #-}
{-# LANGUAGE OverloadedStrings #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -Wno-deferred-out-of-scope-variables #-}

-- | Common functions for parsers of UPLC, PLC, and PIR.

module PlutusCore.Parser.ParserCommon where

import Data.Char (isAlphaNum)
import Data.Map qualified as M
import Data.Text qualified as T
import PlutusPrelude
import Text.Megaparsec hiding (ParseError, State, parse, some)
import Text.Megaparsec.Char (char, letterChar, space1)
import Text.Megaparsec.Char.Lexer qualified as Lex

import Control.Monad.State (MonadState (get, put), StateT, evalStateT)

import Data.ByteString.Internal (packChars)
import Data.ByteString.Lazy (ByteString)
import Data.ByteString.Lazy.Internal (unpackChars)
import PlutusCore.Core.Type
import PlutusCore.Default
import PlutusCore.Error
import PlutusCore.Name
import PlutusCore.Quote

newtype ParserState = ParserState { identifiers :: M.Map T.Text Unique }
    deriving (Show)

type Parser =
    ParsecT ParseError T.Text (StateT ParserState Quote)

instance (Stream s, MonadQuote m) => MonadQuote (ParsecT e s m)

initial :: ParserState
initial = ParserState M.empty

-- | Return the unique identifier of a name.
-- If it's not in the current parser state, map the name to a fresh id
-- and add it to the state. Used in the Name parser.
intern :: (MonadState ParserState m, MonadQuote m)
    => T.Text -> m Unique
intern n = do
    st <- get
    case M.lookup n (identifiers st) of
        Just u -> return u
        Nothing -> do
            fresh <- freshUnique
            let identifiers' = M.insert n fresh $ identifiers st
            put $ ParserState identifiers'
            return fresh

parse :: Parser a -> String -> T.Text -> Either (ParseErrorBundle T.Text ParseError) a
parse p file str = runQuote $ parseQuoted p file str

-- | Generic parser function.
parseGen :: Parser a -> ByteString -> Either (ParseErrorBundle T.Text ParseError) a
parseGen stuff bs = parse stuff "test" $ (T.pack . unpackChars) bs

parseQuoted ::
    Parser a -> String -> T.Text ->
        Quote (Either (ParseErrorBundle T.Text ParseError) a)
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
type PType = Type TyName DefaultUni SourcePos

varType :: Parser PType
varType = TyVar <$> getSourcePos <*> tyName

funType :: Parser PType
funType = TyFun <$> wordPos "fun" <*> pType <*> pType

allType :: Parser PType
allType = TyForall <$> wordPos "all" <*> tyName <*> kind <*> pType

lamType :: Parser PType
lamType = TyLam <$> wordPos "lam" <*> tyName <*> kind <*> pType

ifixType :: Parser PType
ifixType = TyIFix <$> wordPos "ifix" <*> pType <*> pType

builtinType :: Parser PType
builtinType = TyBuiltin <$> wordPos "con" <*> defaultUniType

appType :: Parser PType
appType = do
    pos  <- getSourcePos
    fn   <- pType
    args <- some pType
    pure $ tyApps pos fn args

tyApps :: SourcePos -> PType -> [PType] -> PType
tyApps _  _t []           = error "tyApps: A type application without an argument."
tyApps loc ty [ty']       = TyApp loc ty ty'
tyApps loc ty (ty' : tys) = TyApp loc (tyApps loc ty (ty':init tys)) (last tys)

kind :: Parser (Kind SourcePos)
kind = inParens (typeKind <|> funKind)
    where
        typeKind = Type <$> wordPos "type"
        funKind  = KindArrow <$> wordPos "fun" <*> kind <*> kind

-- | Parser for @PType@.
pType :: Parser PType
pType = choice
    [inParens pType
    , funType
    , ifixType
    , allType
    , builtinType
    , lamType
    , inBrackets appType
    , varType
    ]

defaultUniType :: Parser (SomeTypeIn DefaultUni)
defaultUniType = choice $ map try
  [ inParens defaultUniType
  , SomeTypeIn DefaultUniInteger <$ symbol "integer"
  , SomeTypeIn DefaultUniByteString <$ symbol "bytestring"
  , SomeTypeIn DefaultUniString <$ symbol "string"
  , SomeTypeIn DefaultUniUnit <$ symbol "unit"
  , SomeTypeIn DefaultUniBool <$ symbol "bool"
--   , SomeTypeIn DefaultUniProtoList <$ symbol "list"
--   , SomeTypeIn DefaultUniProtoPair <$ symbol "pair"
  -- , SomeTypeIn DefaultUniApply <$ symbol "?" TODO need to make this an operator
    ]

inParens :: Parser a -> Parser a
inParens = between (symbol "(") (symbol ")")

inBrackets :: Parser a -> Parser a
inBrackets = between (symbol "[") (symbol "]")

inBraces :: Parser a-> Parser a
inBraces = between (symbol "{") (symbol "}")

isIdentifierChar :: Char -> Bool
isIdentifierChar c = isAlphaNum c || c == '_' || c == '\''

-- | Create a parser that matches the input word and returns its source position.
-- This is for attaching source positions to parsed terms/programs.
wordPos ::
    -- | The word to match
    T.Text -> Parser SourcePos
wordPos w = lexeme $ try $ getSourcePos <* symbol w

-- | The list of parsable default functions and their pretty print correspondence.
builtinFnList :: [(DefaultFun, T.Text)]
builtinFnList =
    [ (AddInteger,"addInteger")
    , (SubtractInteger,"subtractInteger")
    , (MultiplyInteger,"multiplyInteger")
    , (DivideInteger,"divideInteger")
    , (QuotientInteger,"quotientInteger")
    , (RemainderInteger,"remainderInteger")
    , (ModInteger,"modInteger")
    , (EqualsInteger,"equalsInteger")
    , (LessThanInteger,"lessThanInteger")
    , (LessThanEqualsInteger,"lessThanEqualsInteger")
    , (AppendByteString,"appendByteString")
    , (ConsByteString,"consByteString")
    , (SliceByteString,"sliceByteString")
    , (LengthOfByteString,"lengthOfByteString")
    , (IndexByteString,"indexByteString")
    , (EqualsByteString,"equalsByteString")
    , (LessThanByteString,"lessThanByteString")
    , (LessThanEqualsByteString,"lessThanEqualsByteString")
    , (Sha2_256,"sha2_256")
    , (Sha3_256,"sha3_256")
    , (Blake2b_256,"blake2b_256")
    , (VerifySignature,"verifySignature")
    , (AppendString,"appendString")
    , (EqualsString,"equalsString")
    , (EncodeUtf8,"encodeUtf8")
    , (DecodeUtf8,"decodeUtf8")
    , (IfThenElse,"ifThenElse")
    , (ChooseUnit,"chooseUnit")
    , (Trace,"trace")
    , (FstPair,"fstPair")
    , (SndPair,"sndPair")
    , (ChooseList,"chooseList")
    , (MkCons,"mkCons")
    , (HeadList,"headList")
    , (TailList,"tailList")
    , (NullList,"nullList")
    , (ChooseData,"chooseData")
    , (ConstrData,"constrData")
    , (MapData,"mapData")
    , (ListData,"listData")
    , (IData,"iData")
    , (BData,"bData")
    , (UnConstrData,"unConstrData")
    , (UnMapData,"unMapData")
    , (UnListData,"unListData")
    , (UnIData,"unIData")
    , (UnBData,"unBData")
    , (EqualsData,"equalsData")
    , (MkPairData,"mkPairData")
    , (MkNilData,"mkNilData")
    , (MkNilPairData,"mkNilPairData")
    ]

builtinFunction :: Parser DefaultFun
builtinFunction =
    choice $
        map
            (try . (\(fn, text) -> fn <$ symbol text))
            builtinFnList

version :: Parser (Version SourcePos)
version = lexeme $ do
    p <- getSourcePos
    x <- Lex.decimal
    void $ char '.'
    y <- Lex.decimal
    void $ char '.'
    Version p x y <$> Lex.decimal

name :: Parser Name
name = lexeme $ try $ do
    void $ lookAhead letterChar
    str <- takeWhileP (Just "identifier") isIdentifierChar
    Name str <$> intern str

tyName :: Parser TyName
tyName = TyName <$> name

-- | Turn a parser that can succeed without consuming any input into one that fails in this case.
enforce :: Parser a -> Parser a
enforce p = do
    (input, x) <- match p
    guard . not $ T.null input
    pure x

signedInteger :: ParsecT ParseError T.Text (StateT ParserState Quote) Integer
signedInteger = Lex.signed whitespace (lexeme Lex.decimal)

-- | Parser for integer constants.
conInt :: Parser (Some (ValueOf DefaultUni))
conInt = do
    con::Integer <- signedInteger
    pure $ someValue con

-- | Parser for bytestring constants. They start with "#".
conBS :: Parser (Some (ValueOf DefaultUni))
conBS = do
    _ <- char '#'
    con <- takeWhileP (Just "builtin bytestring") isHexDigit
    pure $ someValue $ packChars $ T.unpack con

-- | Parser for string constants. They are wrapped in double quotes.
conText :: Parser (Some (ValueOf DefaultUni))
conText = do
    con <- char '\"' *> manyTill Lex.charLiteral (char '\"')
    pure $ someValue $ T.pack con

-- | Parser for unit.
conUnit :: Parser (Some (ValueOf DefaultUni))
conUnit = someValue () <$ symbol "()"

-- | Parser for bool.
conBool :: Parser (Some (ValueOf DefaultUni))
conBool = choice
    [ someValue True <$ symbol "True"
    , someValue False <$ symbol "False"
    ]

--TODO fix these (add parsing of constant after symbol?):
-- conPair :: Parser (Some (ValueOf DefaultUni))
-- conPair = someValue (,) <$ symbol "pair"
-- conList :: Parser (Some (ValueOf DefaultUni))
-- conList = someValue [] <$ symbol "list"
-- conData :: Parser (Some (ValueOf DefaultUni))
-- conData = someValue Data? <$ symbol "data"

constant :: Parser (Some (ValueOf DefaultUni))
constant = choice $ map try
    [ inParens constant
    , conInt
    , conBS
    , conText
    , conUnit
    , conBool
    -- , conPair
    -- , conList
    -- , conData
    ]
