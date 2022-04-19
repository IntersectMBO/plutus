{-# LANGUAGE GADTs             #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}

module PlutusCore.Parser.Builtin where

import Data.Text qualified as T
import Data.Text.Internal.Read (hexDigitToInt)
import PlutusPrelude
import Text.Megaparsec hiding (ParseError, State, parse, some)
import Text.Megaparsec.Char (char, hexDigitChar)
import Text.Megaparsec.Char.Lexer qualified as Lex hiding (hexadecimal)

import Data.ByteString (pack)
import PlutusCore.Default
import PlutusCore.Parser.ParserCommon (Parser, lexeme, symbol, whitespace)
import PlutusCore.Parser.Type (defaultUniType)


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
    , (SerialiseData,"serialiseData")
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

