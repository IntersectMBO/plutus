module Numeric.Read(
  readParen,
  readSigned,
  readInt,
  readBin,
  readDec,
  readOct,
  readHex,
  readIntegral,
  readBoundedEnum,
  ) where
import Data.Bool
import Data.Bounded
import Data.Char
import Data.Enum
import Data.Eq
import Data.Function
import Data.Integral
import Data.List
import Data.Maybe_Type
import Data.Num
import Data.Ord
import Data.String
import Prelude qualified ()
import Primitives
import {-# SOURCE #-} Text.Read.Internal (lex)
import Text.Show

type ReadS a = String -> [(a, String)]

readParen :: forall a . Bool -> ReadS a -> ReadS a
readParen b g =  if b then mandatory else optional
  where optional r  = g r ++ mandatory r
        mandatory r = [(x,u) | ("(",s) <- lex r,
                               (x,t)   <- optional s,
                               (")",u) <- lex t ]

--------------------------------------------------------

readInt :: forall a . Num a => a -> (Char -> Bool)  -> (Char -> Int) -> ReadS a
readInt base isDig valDig cs@(c:_) | isDig c = loop 0 cs
  where loop r (c:cs) | isDig c = loop (r * base + fromIntegral (valDig c)) cs
        loop r ds = [(r, ds)]
readInt _ _ _ _ = []

readBin :: forall a . (Num a) => ReadS a
readBin = readInt 2 isBinDigit digitToInt

isBinDigit :: Char -> Bool
isBinDigit c = c == '0' || c == '1'

readOct :: forall a . (Num a) => ReadS a
readOct = readInt 8 isOctDigit digitToInt

readDec :: forall a . (Num a) => ReadS a
readDec = readInt 10 isDigit digitToInt

readHex :: forall a . (Num a) => ReadS a
readHex = readInt 16 isHexDigit digitToInt

readSigned :: forall a . (Num a) => ReadS a -> ReadS a
readSigned readPos = readParen False read'
  where
    read' :: ReadS a
    read' r  = readPos r ++
               [ (- x, t) | ("-", s) <- lex r, (x, t) <- readPos s ]

readIntegral :: forall a . (Integral a) => Int -> ReadS a
readIntegral _ = readSigned (readAny . dropSpace)
  where readAny ('0':'x':cs) = readHex cs
        readAny ('0':'X':cs) = readHex cs
        readAny ('0':'o':cs) = readOct cs
        readAny ('0':'O':cs) = readOct cs
        readAny ('0':'b':cs) = readBin cs
        readAny ('0':'B':cs) = readBin cs
        readAny cs           = readDec cs

readBoundedEnum :: forall a . (Enum a, Bounded a, Show a) => ReadS a
readBoundedEnum = \ r -> [ (e, t) | (s, t) <- lex r, Just e <- [lookup s table] ]
  where table = [ (show e, e) | e <- [ minBound .. maxBound ] ]

dropSpace :: String -> String
dropSpace = dropWhile isSpace
