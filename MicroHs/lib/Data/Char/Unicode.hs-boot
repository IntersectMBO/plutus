module Data.Char.Unicode where
import Data.Bool_Type
import Data.Char_Type
import Prelude qualified ()

data GeneralCategory

isControl :: Char -> Bool
isPrint :: Char -> Bool
isSpace :: Char -> Bool
isUpper :: Char -> Bool
isLower :: Char -> Bool
isAlpha :: Char -> Bool
isAlphaNum :: Char -> Bool
isNumber :: Char -> Bool
isMark :: Char -> Bool
isSeparator :: Char -> Bool
isPunctuation :: Char -> Bool
isSymbol :: Char -> Bool
toTitle :: Char -> Char
toUpper :: Char -> Char
toLower :: Char -> Char
generalCategory :: Char -> GeneralCategory
