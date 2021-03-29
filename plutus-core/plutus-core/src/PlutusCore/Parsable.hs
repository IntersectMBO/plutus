{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE TypeApplications  #-}

{- | A typeclass which provides a `parseConstant` method to convert Text strings
into objects of the appropriate type. This allows one to define parsers for
literal constants belonging to extensible built-in types without having to
modify the main Plutus Core parser. We expect parseConstant . prettyConst to be
the identity function. -}

module PlutusCore.Parsable
    (
     Parsable(..)
    )
where

import           PlutusPrelude

import           Data.Bits       (shiftL, (.|.))
import           Data.ByteString (ByteString)
import qualified Data.ByteString as BS (pack)
import           Data.Char       (ord)
import           Data.Maybe
import qualified Data.Text       as T
import           Text.Read

parseDefault :: Read a => T.Text -> Maybe a
parseDefault = readMaybe . T.unpack

{-
https://github.com/input-output-hk/plutus/pull/2458

effectfully:
I think what we should do is make Parsable megaparsec-based. Then constant parsers consume as many symbols as they like and we won't need to try to predict in the main parser what is a constant and what is formatting.

kwxm:
If you look in Lexer.x there's extensive commentary about how it parses constants. We could steal the relevant regular expressions from there or reuse the entire lexer. I'm not convinced that letting types do their own lexical analysis is a good idea: doing these things correctly can be quite tricky and if you got it wrong it might mess up the main parser in some subtle way that doesn't show up until you encounter an unexpected situation. The way that it's done at the moment provides reasonably general syntax for constants and I'm fairly confident it's correct. I guess I feel that this is low-level stuff that should be done once and then shut away in a box where it won't cause any trouble.

michaelpj:
I think the parsers are generally not super urgent. I also think it's okay to have them not be totally robust: they're not in the "production" line, we don't really have to worry about users doing arbitrary/malicious things with them. It would be nice if they were really solid, but we can live with a few holes.
-}

-- | A class for things that are parsable. Those include tags for built-in types and constants of
-- such types.
class Parsable a where
    -- | Return Nothing if the string is invalid, otherwise the corresponding value of type a.
    parse :: T.Text -> Maybe a

    parseList :: T.Text -> Maybe [a]
    parseList = error "No default implementation for 'parseList'"

newtype AsParsable a = AsParsable a
instance Parsable a => Read (AsParsable a) where
    readsPrec _ = maybeToList . fmap ((, "") . AsParsable) . parse . T.pack
    readList = maybeToList . fmap ((, "") . fmap AsParsable) . parseList . T.pack

-- newtype DeriveParseList a = DeriveParseList a
-- instance Parsable a => Read (DeriveParseList a) where
--     readsPrec = coerce $ readsPrec @(AsParsable a)

--     parseList = coerce $ parseDefault @[DeriveParseList a]

newtype AsReadMono a = AsReadMono a
instance Read a => Parsable (AsReadMono a) where
    parse = coerce $ parseDefault @a
    parseList = coerce $ parseDefault @[a]

newtype AsReadPoly a = AsReadPoly a
instance Read a => Parsable (AsReadPoly a) where
    parse = coerce $ parseDefault @a

instance Parsable a => Parsable [a] where
    parse = parseList

-- >>> :set -XOverloadedStrings
-- >>> parse "[False, True]" :: Maybe [Bool]
-- Just [False,True]
-- >>> parse "\"abc\"" :: Maybe String
-- Just "abc"
-- >>> parse "[\"abc\"]" :: Maybe [String]
-- *** Exception: No default implementation for 'parseList'
-- CallStack (from HasCallStack):
--   error, called at /tmp/dante19742wSk.hs:53:17 in main:PlutusCore.Parsable
deriving via AsReadMono Bool    instance Parsable Bool
deriving via AsReadMono Char    instance Parsable Char
deriving via AsReadMono Integer instance Parsable Integer
deriving via AsReadMono ()      instance Parsable ()

deriving via AsReadPoly (AsParsable a, AsParsable b)
    instance (Parsable a, Parsable b) => Parsable (a, b)

instance Parsable ByteString where
    parse = parseByteStringConstant



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
