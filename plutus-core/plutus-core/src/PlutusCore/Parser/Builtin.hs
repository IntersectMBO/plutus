{-# LANGUAGE GADTs             #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module PlutusCore.Parser.Builtin where

import Data.Text qualified as T
import Data.Text.Internal.Read (hexDigitToInt)
import PlutusPrelude (Word8)
import Text.Megaparsec (MonadParsec (takeWhileP), choice, customFailure, getSourcePos, many, manyTill)
import Text.Megaparsec.Char (char, hexDigitChar)
import Text.Megaparsec.Char.Lexer qualified as Lex

import Data.ByteString (pack)
import Data.Map.Strict as Map (Map, fromList, lookup, toList)
import PlutusCore.Default
import PlutusCore.Error (ParserError (UnknownBuiltinFunction))
import PlutusCore.Parser.ParserCommon (Parser, isIdentifierChar, lexeme, symbol, whitespace)
import PlutusCore.Parser.Type (defaultUniType)
import PlutusCore.Pretty (display)
import Prelude

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

signedInteger :: Parser Integer
signedInteger = Lex.signed whitespace (lexeme Lex.decimal)

-- | Parser for integer constants.
conInt :: Parser (Some (ValueOf DefaultUni))
conInt = do
    con::Integer <- signedInteger
    pure $ someValue con

-- | Parser for a pair of hex digits to a Word8.
hexByte :: Parser Word8
hexByte = do
    high <- hexDigitChar
    low <- hexDigitChar
    return $ fromIntegral (hexDigitToInt high * 16 + hexDigitToInt low)

-- | Parser for bytestring constants. They start with "#".
conBS :: Parser (Some (ValueOf DefaultUni))
conBS = do
    _ <- char '#'
    bytes <- Text.Megaparsec.many hexByte
    pure $ someValue $ pack bytes

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

-- | Parser for a constant term. Currently the syntax is "con defaultUniType val".
constant :: Parser (Some (ValueOf DefaultUni))
constant = do
    conTy <- defaultUniType
    con <-
        case conTy of --TODO add Lists, Pairs, Data, App
            SomeTypeIn DefaultUniInteger    -> conInt
            SomeTypeIn DefaultUniByteString -> conBS
            SomeTypeIn DefaultUniString     -> conText
            SomeTypeIn DefaultUniUnit       -> conUnit
            SomeTypeIn DefaultUniBool       -> conBool
    whitespace
    pure con

