{-# LANGUAGE GADTs             #-}
{-# LANGUAGE OverloadedStrings #-}

module PlutusCore.Parser.Builtin where

import PlutusPrelude (Word8, reoption)

import PlutusCore.Default
import PlutusCore.Error (ParserError (UnknownBuiltinFunction))
import PlutusCore.Parser.ParserCommon
import PlutusCore.Parser.Type (defaultUniType)
import PlutusCore.Pretty (display)

import Control.Applicative
import Data.ByteString (ByteString, pack)
import Data.Map.Strict qualified as Map
import Data.Text qualified as T
import Data.Text.Internal.Read (hexDigitToInt)
import Text.Megaparsec (MonadParsec (takeWhileP), choice, customFailure, getSourcePos, manyTill)
import Text.Megaparsec.Char (char, hexDigitChar)
import Text.Megaparsec.Char.Lexer qualified as Lex

cachedBuiltin :: Map.Map T.Text DefaultFun
cachedBuiltin = Map.fromList [ (display fn, fn) | fn <- [minBound .. maxBound] ]

-- | Parser for builtin functions. Atm the parser can only parse `DefaultFun`.
builtinFunction :: Parser DefaultFun
builtinFunction = lexeme $ do
    txt <- takeWhileP (Just "builtin function identifier") isIdentifierChar
    case Map.lookup txt cachedBuiltin of
        Nothing      -> do
            let lBuiltin = fmap fst $ Map.toList cachedBuiltin
            pos <- getSourcePos
            customFailure $ UnknownBuiltinFunction txt pos lBuiltin
        Just builtin -> pure builtin

-- | Parser for integer constants.
conInteger :: Parser Integer
conInteger = Lex.signed whitespace (lexeme Lex.decimal)

-- | Parser for a pair of hex digits to a Word8.
hexByte :: Parser Word8
hexByte = do
    high <- hexDigitChar
    low <- hexDigitChar
    pure $ fromIntegral (hexDigitToInt high * 16 + hexDigitToInt low)

-- | Parser for bytestring constants. They start with "#".
conBS :: Parser ByteString
conBS = lexeme . fmap pack $ char '#' *> many hexByte

-- | Parser for string constants. They are wrapped in double quotes.
conText :: Parser T.Text
conText = lexeme . fmap T.pack $ char '\"' *> manyTill Lex.charLiteral (char '\"')

-- | Parser for unit.
conUnit :: Parser ()
conUnit = () <$ (symbol "(" *> symbol ")")

-- | Parser for bool.
conBool :: Parser Bool
conBool = choice
    [ True <$ symbol "True"
    , False <$ symbol "False"
    ]

-- Taken verbatim from https://hackage.haskell.org/package/parsec-3.1.15.1/docs/Text-Parsec-Combinator.html#v:sepBy
sepBy :: Alternative m => m a -> m sep -> m [a]
sepBy p sep = sepBy1 p sep <|> pure []
sepBy1 :: Alternative m => m a -> m sep -> m [a]
sepBy1 p sep = (:) <$> p <*> many (sep *> p)

conList :: DefaultUni (Esc a) -> Parser [a]
conList uniA = inBrackets $ constantOf uniA `sepBy` symbol ","

conPair :: DefaultUni (Esc a) -> DefaultUni (Esc b) -> Parser (a, b)
conPair uniA uniB = inParens $ do
    a <- constantOf uniA
    _ <- symbol ","
    b <- constantOf uniB
    pure (a, b)

constantOf :: DefaultUni (Esc a) -> Parser a
constantOf uni = case uni of
    DefaultUniInteger                                                 -> conInteger
    DefaultUniByteString                                              -> conBS
    DefaultUniString                                                  -> conText
    DefaultUniUnit                                                    -> conUnit
    DefaultUniBool                                                    -> conBool
    DefaultUniProtoList `DefaultUniApply` uniA                        -> conList uniA
    DefaultUniProtoPair `DefaultUniApply` uniA `DefaultUniApply` uniB -> conPair uniA uniB
    f `DefaultUniApply` _ `DefaultUniApply` _ `DefaultUniApply` _     -> noMoreTypeFunctions f
    DefaultUniData                                                    ->
        error "Data not supported"

constant :: Parser (Some (ValueOf DefaultUni))
constant = do
    SomeTypeIn (Kinded uni) <- defaultUniType
    Refl <- reoption $ checkStar uni
    someValueOf uni <$> constantOf uni
