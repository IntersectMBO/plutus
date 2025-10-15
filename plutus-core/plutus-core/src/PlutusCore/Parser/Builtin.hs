{-# LANGUAGE GADTs             #-}
{-# LANGUAGE OverloadedStrings #-}

module PlutusCore.Parser.Builtin where

import PlutusPrelude (Word8, reoption, void)

import PlutusCore.Builtin.Result qualified
import PlutusCore.Crypto.BLS12_381.G1 qualified as BLS12_381.G1
import PlutusCore.Crypto.BLS12_381.G2 qualified as BLS12_381.G2
import PlutusCore.Data
import PlutusCore.Default
import PlutusCore.Error (ParserError (UnknownBuiltinFunction))
import PlutusCore.Name.Unique
import PlutusCore.Parser.ParserCommon
import PlutusCore.Parser.Type (defaultUni)
import PlutusCore.Pretty (display)
import PlutusCore.Value qualified as PLC (Value)
import PlutusCore.Value qualified as Value

import Control.Monad.Combinators
import Data.ByteString (ByteString, pack, unpack)
import Data.Map.Strict qualified as Map
import Data.Text qualified as T
import Data.Text.Internal.Read (hexDigitToInt)
import Data.Vector.Strict (Vector)
import Data.Vector.Strict qualified as Vector
import Text.Megaparsec (customFailure, getSourcePos, takeWhileP)
import Text.Megaparsec.Char (char, hexDigitChar, string)
import Text.Megaparsec.Char.Lexer qualified as Lex

cachedBuiltin :: Map.Map T.Text DefaultFun
cachedBuiltin = Map.fromList [(display fn, fn) | fn <- [minBound .. maxBound]]

-- | Parser for builtin functions. Atm the parser can only parse `DefaultFun`.
builtinFunction :: Parser DefaultFun
builtinFunction = lexeme $ do
  txt <- takeWhileP (Just "builtin function identifier") isIdentifierChar
  case Map.lookup txt cachedBuiltin of
    Nothing -> do
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

{- | Parser for string constants (wrapped in double quotes).  Note that
 Data.Text.pack "performs replacement on invalid scalar values", which means
 that Unicode surrogate code points (corresponding to integers in the range
 0xD800-0xDFFF) are converted to the Unicode replacement character U+FFFD
 (decimal 65533).  Thus `(con string "X\xD800Z")` parses to a `Text` object
 whose second character is U+FFFD.
-}
conText :: Parser T.Text
conText = lexeme . fmap T.pack $ char '\"' *> manyTill Lex.charLiteral (char '\"')

-- | Parser for unit.
conUnit :: Parser ()
conUnit = void (symbol "(" *> symbol ")")

-- | Parser for bool.
conBool :: Parser Bool
conBool =
  choice
    [ True <$ symbol "True"
    , False <$ symbol "False"
    ]

-- | Parser for lists.
conList :: DefaultUni (Esc a) -> Parser [a]
conList uniA = trailingWhitespace . inBrackets $
  constantOf ExpectParensNo uniA `sepBy` symbol ","

-- | Parser for arrays.
conArray :: DefaultUni (Esc a) -> Parser (Vector a)
conArray uniA = Vector.fromList <$> conList uniA

-- | Parser for values.
conValue :: Parser PLC.Value
conValue = do
  keys <- traverse validateKeys =<< conList knownUni
  case Value.fromList keys of
    PlutusCore.Builtin.Result.BuiltinSuccess v -> pure v
    PlutusCore.Builtin.Result.BuiltinSuccessWithLogs _logs v -> pure v
    PlutusCore.Builtin.Result.BuiltinFailure logs _trace ->
      fail $ "Failed to construct Value: " <> show logs
 where
  validateToken (token, amt) = do
    tk <- maybe (fail $ "Token name exceeds maximum length of 32 bytes: " <> show (unpack token))
               pure (Value.k token)
    qty <- maybe (fail $ "Token quantity out of signed 128-bit integer bounds: " <> show amt)
                pure (Value.quantity amt)
    pure (tk, qty)
  validateKeys (currency, tokens) = do
    ck <- maybe (fail $ "Currency symbol exceeds maximum length of 32 bytes: " <> show (unpack currency))
                pure (Value.k currency)
    tks <- traverse validateToken tokens
    pure (ck, tks)

-- | Parser for pairs.
conPair :: DefaultUni (Esc a) -> DefaultUni (Esc b) -> Parser (a, b)
conPair uniA uniB = trailingWhitespace . inParens $ do
  a <- constantOf ExpectParensNo uniA
  _ <- symbol ","
  b <- constantOf ExpectParensNo uniB
  pure (a, b)

conDataNoParens :: Parser Data
conDataNoParens =
    choice
        [ symbol "Constr" *> (Constr <$> conInteger <*> conList knownUni)
        , symbol "Map" *> (Map <$> conList knownUni)
        , symbol "List" *> (List <$> conList knownUni)
        , symbol "I" *> (I <$> conInteger)
        , symbol "B" *> (B <$> conBS)
        ]

conData :: ExpectParens -> Parser Data
conData ExpectParensYes = trailingWhitespace $ inParens conDataNoParens
conData ExpectParensNo  = conDataNoParens

-- Serialised BLS12_381 elements are "0x" followed by a hex string of even
-- length.  Maybe we should just use the usual bytestring syntax.
con0xBS :: Parser ByteString
con0xBS = lexeme . fmap pack $ string "0x" *> many hexByte

conBLS12_381_G1_Element :: Parser BLS12_381.G1.Element
conBLS12_381_G1_Element = do
    s <- con0xBS
    case BLS12_381.G1.uncompress s of
      Left err -> fail $ "Failed to decode value of type bls12_381_G1_element: " ++ show err
      Right e  -> pure e

conBLS12_381_G2_Element :: Parser BLS12_381.G2.Element
conBLS12_381_G2_Element = do
    s <- con0xBS
    case BLS12_381.G2.uncompress s of
      Left err -> fail $ "Failed to decode value of type bls12_381_G2_element: " ++ show err
      Right e  -> pure e

-- | Parser for constants of the given type.
constantOf :: ExpectParens -> DefaultUni (Esc a) -> Parser a
constantOf expectParens uni =
  case uni of
    DefaultUniInteger                                                 -> conInteger
    DefaultUniByteString                                              -> conBS
    DefaultUniString                                                  -> conText
    DefaultUniUnit                                                    -> conUnit
    DefaultUniBool                                                    -> conBool
    DefaultUniValue                                                   -> conValue
    DefaultUniProtoList `DefaultUniApply` uniA                        -> conList uniA
    DefaultUniProtoArray `DefaultUniApply` uniA                       -> conArray uniA
    DefaultUniProtoPair `DefaultUniApply` uniA `DefaultUniApply` uniB -> conPair uniA uniB
    f `DefaultUniApply` _ `DefaultUniApply` _ `DefaultUniApply` _     -> noMoreTypeFunctions f
    DefaultUniData                                                    -> conData expectParens
    DefaultUniBLS12_381_G1_Element                                    -> conBLS12_381_G1_Element
    DefaultUniBLS12_381_G2_Element                                    -> conBLS12_381_G2_Element
    DefaultUniBLS12_381_MlResult
        -> fail "Constants of type bls12_381_mlresult are not supported"

-- | Parser of constants whose type is in 'DefaultUni'.
constant :: Parser (Some (ValueOf DefaultUni))
constant = do
  -- Parse the type tag.
  SomeTypeIn (Kinded uni) <- defaultUni
  -- Check it's of kind @*@, because a constant that we're about to parse can only be of type of
  -- kind @*@.
  Refl <- reoption $ checkStar uni
  -- Parse the constant of the type represented by the type tag.
  someValueOf uni <$> constantOf ExpectParensYes uni

data ExpectParens
  = ExpectParensYes
  | ExpectParensNo
