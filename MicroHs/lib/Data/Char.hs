-- Copyright 2023 Lennart Augustsson
-- See LICENSE file for full license.
module Data.Char(
  Char, String,
  chr, ord,
  isLower, isUpper,
  isAsciiLower, isAsciiUpper,
  isAlpha, isLetter, isAlphaNum,
  isDigit, isOctDigit, isHexDigit,
  isNumber,
  isSymbol, isPunctuation,
  isSpace,
  isControl,
  U.isMark,
  isSeparator,
  isAscii, isLatin1,
  isPrint,
  U.GeneralCategory(..),
  U.generalCategory,
  digitToInt,
  intToDigit,
  toLower, toUpper, toTitle,
  showLitChar,
  -- lexLitChar, readLitChar,
  -- XXX For now, don't import Text.Read, it's a bloated beast.
  ) where
import qualified Prelude()              -- do not import Prelude
import Primitives
import Control.Error
import Data.Bool
import Data.Bounded
import Data.Char_Type
import {-# SOURCE #-} qualified Data.Char.Unicode as U
import Data.Eq
import Data.Function
import Data.Int
import Data.List_Type
import Data.Num
import Data.Ord
--import {-# SOURCE #-} Text.Read.Internal (lexLitChar, readLitChar)
-- XXX For now, don't import Text.Read, it's a bloated beast.
import Text.Show

instance Eq Char where
  (==) = primCharEQ
  (/=) = primCharNE

instance Ord Char where
  compare = primCharCompare
  (<)  = primCharLT
  (<=) = primCharLE
  (>)  = primCharGT
  (>=) = primCharGE

-- Using primitive comparison is still a small speedup, even using mostly bytestrings
instance Eq String where
  (==) = primStringEQ

instance Ord String where
  compare =  primStringCompare
  x <  y  =  case primStringCompare x y of { LT -> True; _ -> False }
  x <= y  =  case primStringCompare x y of { GT -> False; _ -> True }
  x >  y  =  case primStringCompare x y of { GT -> True; _ -> False }
  x >= y  =  case primStringCompare x y of { LT -> False; _ -> True }

instance Bounded Char where
  minBound = primChr 0
  maxBound = primChr 0x10ffff

chr :: Int -> Char
chr i
  | primIntToWord i `primWordLE` 0x10ffff = primChr i
  | otherwise = error "Data.Char.chr: invalid codepoint"

ord :: Char -> Int
ord = primOrd

isLower :: Char -> Bool
isLower c =
  if primCharLE c '\177' then
     isAsciiLower c
  else
     U.isLower c

isAsciiLower :: Char -> Bool
isAsciiLower c = 'a' <= c && c <= 'z'

isUpper :: Char -> Bool
isUpper c =
  if isAscii c then
    isAsciiUpper c
  else
    U.isUpper c

isAsciiUpper :: Char -> Bool
isAsciiUpper c = 'A' <= c && c <= 'Z'

isAlpha :: Char -> Bool
isAlpha c =
  if isAscii c then
    isLower c || isUpper c
  else
    U.isAlpha c

isLetter :: Char -> Bool
isLetter = isAlpha

isDigit :: Char -> Bool
isDigit c = '0' <= c && c <= '9'

isOctDigit :: Char -> Bool
isOctDigit c = '0' <= c && c <= '7'

isHexDigit :: Char -> Bool
isHexDigit c = isDigit c || ('a' <= c && c <= 'f') || ('A' <= c && c <= 'F')

isAlphaNum :: Char -> Bool
isAlphaNum c =
  if isAscii c then
    isAlpha c || isDigit c
  else
    U.isAlphaNum c

isNumber :: Char -> Bool
isNumber c =
  if isAscii c then
    isDigit c
  else
    U.isNumber c

isSymbol :: Char -> Bool
isSymbol c =
 if isAscii c then
   c `xelem` "$+<=>^`|~"
 else
   U.isSymbol c

isPunctuation :: Char -> Bool
isPunctuation c =
  if isAscii c then
    c `xelem` "!\"#%&'()*,-./:;?@[\\]_{}"
  else
    U.isPunctuation c

-- Don't want to import Data.List
xelem :: Char -> [Char] -> Bool
xelem _ [] = False
xelem d (c:cs) = d == c || xelem d cs

isPrint :: Char -> Bool
isPrint c =
  if isAscii c then
    ' ' <= c && c <= '~'
  else
    U.isPrint c

isSpace :: Char -> Bool
isSpace c =
  if isAscii c then
    c `xelem` " \t\n\v\f\r"
  else
    U.isSpace c

isControl :: Char -> Bool
isControl c = c <= '\31' || c == '\127'

isSeparator :: Char -> Bool
isSeparator c =
  if isAscii c then
    c == ' '
  else
    U.isSeparator c

isAscii :: Char -> Bool
isAscii c = c <= '\127'

isLatin1 :: Char -> Bool
isLatin1 c = c <= '\255'

digitToInt :: Char -> Int
digitToInt c | primCharLE '0' c && primCharLE c '9' = ord c - ord '0'
             | primCharLE 'a' c && primCharLE c 'f' = ord c - (ord 'a' - 10)
             | primCharLE 'A' c && primCharLE c 'F' = ord c - (ord 'A' - 10)
             | otherwise                            = error "digitToInt"

intToDigit :: Int -> Char
intToDigit i | i < 10 = primChr (ord '0' + i)
             | otherwise = primChr (ord 'A' - 10 + i)

toLower :: Char -> Char
toLower c | isAsciiUpper c = primChr (ord c - ord 'A' + ord 'a')
          | isAscii c = c
          | True = U.toLower c

toUpper :: Char -> Char
toUpper c | isAsciiLower c = primChr (ord c - ord 'a' + ord 'A')
          | isAscii c = c
          | True = U.toUpper c

toTitle :: Char -> Char
toTitle c | isAsciiLower c = primChr (ord c - ord 'a' + ord 'A')
          | isAscii c = c
          | True = U.toTitle c

instance Show Char where
  showsPrec _ '\'' = showString "'\\''"
  showsPrec _ c = showChar '\'' . showLitChar c . showChar '\''
  showList    s = showChar '"'  . f s
    where f [] = showChar '"'
          f (c:cs) =
            if c == '"' then showString "\\\"" . f cs
            else showLitChar c . f cs

showLitChar :: Char -> ShowS
showLitChar c s | isAscii c && isPrint c && c /= '\\' = c : s
showLitChar c rest =
  let
    needDigitProtect =
      case rest of
        [] -> False
        c : _ -> isDigit c
    needHProtect =
      case rest of
        'H' : _ -> True
        _ -> False
    spec :: [(Char, String)]
    spec = [('\NUL', "NUL"), ('\SOH', "SOH"), ('\STX', "STX"),
            ('\ETX', "ETX"), ('\EOT', "EOT"), ('\ENQ', "ENQ"), ('\ACK', "ACK"),
            ('\a', "a"), ('\b', "b"), ('\t', "t"), ('\n', "n"),
            ('\v', "v"), ('\f', "f"), ('\r', "r"), ('\\', "\\"),
            ('\SO', "SO"), ('\SI', "SI"), ('\DLE', "DLE"), ('\DC1', "DC1"), ('\DC2', "DC2"),
            ('\DC3', "DC3"), ('\DC4', "DC4"), ('\NAK', "NAK"), ('\SYN', "SYN"),
            ('\ETB', "ETB"), ('\CAN', "CAN"), ('\EM', "EM"), ('\SUB', "SUB"),
            ('\ESC', "ESC"), ('\FS', "FS"), ('\GS', "GS"), ('\RS', "RS"), ('\US', "US"),
            ('\DEL', "DEL")
           ]
    look [] = ("\\"::String) ++ show (ord c) ++ if needDigitProtect then "\\&"::String else ""
    look ((d,s):xs) = if d == c then '\\':s ++ (if c == '\SO' && needHProtect then "\\&"::String else "") else look xs
  in look spec ++ rest
