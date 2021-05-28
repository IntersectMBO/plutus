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
import qualified Data.Text       as T
import           Text.Read

{- Note [Parsing horribly broken]
As the title suggests, at the moment parsing is horribly broken. 'parse' expects a closed chunk of
text, but in order to provide one we need to determine in the main parsing pipeline (which can be
Happy-based or megaparsec-based) where that closed chunk ends (determining where it starts is easy).
So we need either of these two:

1. perform lexical analysis, cut the right piece and feed it to 'parse'
2. make 'parse' take as much as it needs and return the rest to the main parsing machinery

The latter option is quite non-trivial, because we have that Happy parser and it's hard to poke a
hole in it to get some custom parsing of constants consuming an arbitrary amount of symbols
(we don't even have symbols in Happy -- it's tokens there). So if we wanted to do the latter,
it would probably be the easiest option to just remove the Happy parser and replace it with a
megaparsec-based one (should be the simplest thing in the world, given that PIR is a superset of
PLC and already has a megaparsec-based parser).

There are arguments in favor of the former option (https://github.com/input-output-hk/plutus/pull/2458#discussion_r522091227):

> If you look in Lexer.x there's extensive commentary about how it parses constants. We could steal
the relevant regular expressions from there or reuse the entire lexer. I'm not convinced that
letting types do their own lexical analysis is a good idea: doing these things correctly can be
quite tricky and if you got it wrong it might mess up the main parser in some subtle way that
doesn't show up until you encounter an unexpected situation. The way that it's done at the moment
provides reasonably general syntax for constants and I'm fairly confident it's correct. I guess I
feel that this is low-level stuff that should be done once and then shut away in a box where it
won't cause any trouble.

however it's not that simple. Consider a list of lists: let's say the lexer determines what
constitutes a closed chunk of text representing such a value. And we feed that chunk to 'parse'.
But now we need to do lexical analysis again, but this time in 'parse' to determine whether a @,@
is a part of formatting or is inside an element (being, say, a string or a list of strings) of the
list. I.e. our constant parsers can be recursive and it's a pain to deal with when you do all the
lexical analysis upfront.

So at the moment we don't do anything correctly. Neither PLC nor PIR can handle lists of lists
and none of them can handle tuples at all ('Read' provides us with overloaded parsing for lists
but not tuples, hence the difference) and PIR, doing its own broken lexical analysis, fails on
things like @(con string "yes (no)")@.

This mess needs to be fixed at some point. It seems that dumping Happy and using megaparsec
eveywhere and making 'Parsable' megaparsec-based would be the simplest option and we don't
really care about the efficiency of the parser.
-}

parseDefault :: Read a => T.Text -> Maybe a
parseDefault = readMaybe . T.unpack

-- | A class for things that are parsable. Those include tags for built-in types and constants of
-- such types.
class Parsable a where
    -- | Return Nothing if the string is invalid, otherwise the corresponding value of type a.
    parse :: T.Text -> Maybe a

    -- | Overloading parsing for lists to special-case 'String' (the GHC's billion dollar mistake).
    parseList :: T.Text -> Maybe [a]
    parseList text =
        error $ "Parsing of lists of this type is not implemented. Caused by: " ++
            T.unpack text

newtype AsRead a = AsRead a
instance Read a => Parsable (AsRead a) where
    parse     = coerce $ parseDefault @a
    parseList = coerce $ parseDefault @[a]

instance Parsable a => Parsable [a] where
    parse = parseList

-- >>> :set -XOverloadedStrings
-- >>> parse "[False, True]" :: Maybe [Bool]
-- Just [False,True]
-- >>> parse "\"abc\"" :: Maybe String
-- Just "abc"
-- >>> parse "[\"abc\"]" :: Maybe [String]
-- *** Exception: Parsing of lists of this type is not implemented. Caused by: ["abc"]
-- CallStack (from HasCallStack):
--   error, called at /tmp/dante13247OOZ.hs:83:9 in main:PlutusCore.Parsable
-- >>> parse "(1, False)" :: Maybe (Integer, Bool)
-- Nothing
deriving via AsRead Bool    instance Parsable Bool
deriving via AsRead Char    instance Parsable Char
deriving via AsRead Integer instance Parsable Integer
deriving via AsRead ()      instance Parsable ()

instance Parsable (a, b) where
    parse = error "Parsing for tuples is not implemented"

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
