--module UniParse where
import Data.Bits
import Data.Char
import Data.Maybe
import Numeric
import System.Environment
import System.IO
import System.Compress

{-
Field  Name  Status Explanation

0	Code value	normative	Code value in 4-digit hexadecimal format.
1	Character name	normative	These names match exactly the names published in Chapter 7 of the Unicode Standard, Version 2.0, except for the two additional characters.
2	General category	normative / informative
(see below)	This is a useful breakdown into various "character types" which can be used as a default categorization in implementations. See below for a brief explanation.
3	Canonical combining classes	normative	The classes used for the Canonical Ordering Algorithm in the Unicode Standard. These classes are also printed in Chapter 4 of the Unicode Standard.
4	Bidirectional category	normative	See the list below for an explanation of the abbreviations used in this field. These are the categories required by the Bidirectional Behavior Algorithm in the Unicode Standard. These categories are summarized in Chapter 3 of the Unicode Standard.
5	Character decomposition mapping	normative	In the Unicode Standard, not all of the mappings are full (maximal) decompositions. Recursive application of look-up for decompositions will, in all cases, lead to a maximal decomposition. The decomposition mappings match exactly the decomposition mappings published with the character names in the Unicode Standard.
6	Decimal digit value	normative	This is a numeric field. If the character has the decimal digit property, as specified in Chapter 4 of the Unicode Standard, the value of that digit is represented with an integer value in this field
7	Digit value	normative	This is a numeric field. If the character represents a digit, not necessarily a decimal digit, the value is here. This covers digits which do not form decimal radix forms, such as the compatibility superscript digits
8	Numeric value	normative	This is a numeric field. If the character has the numeric property, as specified in Chapter 4 of the Unicode Standard, the value of that character is represented with an integer or rational number in this field. This includes fractions as, e.g., "1/5" for U+2155 VULGAR FRACTION ONE FIFTH Also included are numerical values for compatibility characters such as circled numbers.
8	Mirrored	normative	If the character has been identified as a "mirrored" character in bidirectional text, this field has the value "Y"; otherwise "N". The list of mirrored characters is also printed in Chapter 4 of the Unicode Standard.
10	Unicode 1.0 Name	informative	This is the old name as published in Unicode 1.0. This name is only provided when it is significantly different from the Unicode 3.0 name for the character.
11	10646 comment field	informative	This is the ISO 10646 comment field. It is in parantheses in the 10646 names list.
12	Uppercase mapping	informative	Upper case equivalent mapping. If a character is part of an alphabet with case distinctions, and has an upper case equivalent, then the upper case equivalent is in this field. See the explanation below on case distinctions. These mappings are always one-to-one, not one-to-many or many-to-one. This field is informative.
13	Lowercase mapping	informative	Similar to Uppercase mapping
14	Titlecase mapping	informative	Similar to Uppercase mapping


Normative Categories
Abbr.

Description

Lu	Letter, Uppercase
Ll	Letter, Lowercase
Lt	Letter, Titlecase
Mn	Mark, Non-Spacing
Mc	Mark, Spacing Combining
Me	Mark, Enclosing
Nd	Number, Decimal Digit
Nl	Number, Letter
No	Number, Other
Zs	Separator, Space
Zl	Separator, Line
Zp	Separator, Paragraph
Cc	Other, Control
Cf	Other, Format
Cs	Other, Surrogate
Co	Other, Private Use
Cn	Other, Not Assigned (no characters in the file have this property)
Informative Categories
Abbr.

Description

Lm	Letter, Modifier
Lo	Letter, Other
Pc	Punctuation, Connector
Pd	Punctuation, Dash
Ps	Punctuation, Open
Pe	Punctuation, Close
Pi	Punctuation, Initial quote (may behave like Ps or Pe depending on usage)
Pf	Punctuation, Final quote (may behave like Ps or Pe depending on usage)
Po	Punctuation, Other
Sm	Symbol, Math
Sc	Symbol, Currency
Sk	Symbol, Modifier
So	Symbol, Other

-}

data GeneralCategory
  = Lu | Ll | Lt | Mn | Mc | Me | Nd | Nl | No | Zs | Zl | Zp | Cc | Cf | Cs | Co | Cn
  | Lm | Lo | Pc | Pd | Ps | Pe | Pi | Pf | Po | Sm | Sc | Sk | So
  | Xx
  deriving (Eq, Ord, Enum, Show, Bounded)


-- See https://www.unicode.org/L2/L1999/UnicodeData.html for information
unicodeData :: FilePath
unicodeData = "UnicodeData.txt"

main :: IO ()
main = do
  args <- getArgs
  let unifilename =
        case args of
          [] -> unicodeData
          [s] -> s
          _ -> error "usage: Uniparse [File]"
  unifile <- readFile unifilename
  let info = map parseCodePoint $ lines unifile
  --print gcTable
  --mapM_ print info
  let out = encodeGCInfo info
      cout = {-compress $-} compressRLE out
  putStrLn $ "compressedGCTable :: ByteString\ncompressedGCTable =\n  " ++ showChars cout
  let tcInfo = [(cp, t - cp) | (cp, _, _, _, Just t) <- info]
      tcInfoC = delta $ compact tcInfo
  putStrLn $ "\ntcTable :: [(Int, Int, Int)]\ntcTable =\n  " ++ show tcInfoC
  let ucInfo = [(cp, u - cp) | (cp, _, Just u, _, _) <- info]
      ucInfoC = delta $ compact ucInfo
  putStrLn $ "\nucTable :: [(Int, Int, Int)]\nucTable =\n  " ++ show ucInfoC
  let lcInfo = [(cp, l - cp) | (cp, _, _, Just l, _) <- info]
      lcInfoC = delta $ compact lcInfo
  putStrLn $ "\nlcTable :: [(Int, Int, Int)]\nlcTable =\n  " ++ show lcInfoC

-- Use numeric codes, it's a little faster to parse
showChars :: [Char] -> String
showChars cs = '"' : foldr show1 "\"" cs
  where show1 c r | isPrint c && isAscii c =
                                if c == '\\' || c == '"'
                                then '\\' : c : r
                                else c : r
{-
                  | c `elem` "\n\a\b\f\r\t\v"
                    || c >= '\DEL'            = (init $ tail $ show c) ++ r
-}
                  | otherwise = '\\' : show (ord c) ++ prot r
        prot r@(c : _) | isDigit c = '\\' : '&' : r
        prot r = r
                  
{-
showChars cs = "\"" ++ concatMap char cs ++ "\""
  where char c | isPrint c && c /= '\\' && c /= '"' = [c]
               | otherwise = '\\' : show c
-}

type CodePoint = Int
type Info = (CodePoint, GeneralCategory, Maybe CodePoint, Maybe CodePoint, Maybe CodePoint)

parseCodePoint :: String -> Info
parseCodePoint s =
  case splitBy ';' s of
    [   codeValue
      , characterName
      , generalCategory
      , canonicalCombiningClasses
      , bidirectionalCategory
      , characterDecompositionMapping
      , decimalDigitValue
      , digitValue
      , numericValue
      , mirrored
      , unicode1_0Name
      , _10646CommentField
      , uppercaseMapping
      , lowercaseMapping
      , titlecaseMapping
      ] -> (readHex' codeValue, parseCategory generalCategory, readHexM uppercaseMapping, readHexM lowercaseMapping, readHexM titlecaseMapping)
    _ -> error $ "parseCodePoint: " ++ show s

readHexM :: String -> Maybe Int
readHexM "" = Nothing
readHexM s = Just $ readHex' s

readHex' :: String -> Int
readHex' s =
  case readHex s of
    [(i, "")] -> i
    _ -> error $ "readHex': " ++ show s

splitBy :: Eq a => a -> [a] -> [[a]]
splitBy sep = loop []
  where loop r [] = [reverse r]
        loop r (c:cs) | c == sep  = reverse r : loop [] cs
                      | otherwise = loop (c:r) cs

parseCategory :: String -> GeneralCategory
parseCategory s = fromMaybe (error $ "parseCategory: " ++ show s) $ lookup s gcTable

gcTable :: [(String, GeneralCategory)]
gcTable = [ (show x, x) | x <- [ minBound .. maxBound ] ]

encodeGCInfo :: [Info] -> [Char]
encodeGCInfo = enc 0
  where enc  _             []          = []
        enc li ics@((i, _, _, _, _):_) | li < i = put Cn : enc (li+1) ics
        enc  _     ((i, c, _, _, _):ics)        = put  c : enc ( i+1) ics
        put :: GeneralCategory -> Char
        put = toEnum . fromEnum

type Delta = Int

compact :: [(CodePoint, Delta)] -> [(CodePoint, CodePoint, Delta)]
compact [] = []
compact ((c, d) : cds) =
  case range c d cds of
    (c', rcds) -> (c, c', d) : compact rcds
  where
    range c d ((c', d') : cds)
      | c' == c + 1 && d' == d = range c' d cds
    range c d cds = (c, cds)

-- Use deltas instead of absolute numbers.
-- This gives smaller numbers, and also a lot of repetitions (good for LZ encoding).
-- Also, use zig-zag encoding for the incoming delta to avoid negative numbers.
-- Why? Negation makes the type checker slow down a lot. :(
-- Also, fewer characters in the generated code.
delta :: [(CodePoint, CodePoint, Delta)] -> [(Delta, Delta, Delta)]
delta = loop 0
  where loop _ [] = []
        loop o ((l, h, d):xs) = (l - o, h - l, zigZagEncode d) : loop l xs

-- Do
--   (x >> (n-1)) ^ (x << 1)
-- this moves the sign bit into the LSB.
-- Due to the range, we know that the left shift doesn't
-- shift anything into the sign bit.
-- E.g., n=8, x=-2=0xfe
--  (0xfe >> 7) ^ (0xfe << 1) = 0xff ^ 0xfc = 3
-- E.g. n=8, x=2=0x02
--  (0x02 >> 7) ^ (0x02 << 1) = 0x00 ^ 0x04 = 4
zigZagEncode :: Int -> Int
zigZagEncode x = (x `unsafeShiftR` (_wordSize - 1)) `xor` (x `unsafeShiftL` 1)
