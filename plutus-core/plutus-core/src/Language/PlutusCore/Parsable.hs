{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}

{- | A typeclass which provides a `parseConstant` method to convert Text strings
into objects of the appropriate type. This allows one to define parsers for
literal constants belonging to extensible built-in types without having to
modify the main Plutus Core parser. We expect parseConstant . prettyConst to be
the identity function. -}

module Language.PlutusCore.Parsable
    (
     Parsable(..)
    )
where

import           PlutusPrelude

import           Data.Bits       (shiftL, (.|.))
import           Data.ByteString (ByteString)
import qualified Data.ByteString as BS (pack)
import           Data.Char       (ord)
import qualified Data.Text       as T
import           Text.Read       (readMaybe)

-- | A class for things that are parsable. Those include tags for built-in types and constants of
-- such types.
class Parsable a where
    parse :: T.Text -> Maybe a
    -- ^ Return Nothing if the string is invalid, otherwise the corresponding value of type a.
    default parse :: Read a => T.Text -> Maybe a
    parse = readMaybe . T.unpack
    -- ^ The default implementation is in terms of 'Read'.

instance Parsable Bool
instance Parsable Char
instance Parsable Integer
instance Parsable String
instance Parsable ()

instance Parsable ByteString
  where parse = parseByteStringConstant


--- Parsing bytestrings ---

-- A literal bytestring consists of the '#' character followed immediately by
-- an even number of upper- or lower-case hex digits.
parseByteStringConstant :: T.Text -> Maybe ByteString
parseByteStringConstant lit = do
    case T.unpack lit of
        '#':body -> asBSLiteral body
        _        -> Nothing

-- | Convert a list to a list of pairs, failing if the input list has an odd number of elements
pairs :: [a] -> Maybe [(a,a)]
pairs []         = Just []
pairs (a:b:rest) = ((a,b):) <$> pairs rest
pairs _          = Nothing

hexDigitToWord8 :: Char -> Maybe Word8
hexDigitToWord8 c =
    let x = ord8 c
    in    if '0' <= c && c <= '9'  then  Just $ x - ord8 '0'
    else  if 'a' <= c && c <= 'f'  then  Just $ x - ord8 'a' + 10
    else  if 'A' <= c && c <= 'F'  then  Just $ x - ord8 'A' + 10
    else  Nothing

    where ord8 :: Char -> Word8
          ord8 = fromIntegral . Data.Char.ord

-- | Convert a String into a ByteString, failing if the string has odd length
-- or any of its characters are not hex digits
asBSLiteral :: String -> Maybe ByteString
asBSLiteral s =
    mapM hexDigitToWord8 s >>= pairs      -- convert s into a list of pairs of Word8 values in [0..0xF]
    <&> map (\(a,b) -> shiftL a 4 .|. b)  -- convert pairs of values in [0..0xF] to values in [0..xFF]
    <&> BS.pack
