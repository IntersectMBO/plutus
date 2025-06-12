-- Copyright 2023,2024 Lennart Augustsson
-- See LICENSE file for full license.
module Text.Show(module Text.Show) where
import Data.Bool_Type
import Data.Char_Type
import Data.List_Type
import Prelude qualified ()
import Primitives

type ShowS = String -> String

class Show a where
  showsPrec :: Int -> a -> ShowS
  show      :: a -> String
  showList  :: [a] -> ShowS

  showsPrec _ x s = show x ++ s
  show x          = shows x ""
  showList        = showListWith shows

shows :: forall a . Show a => a -> ShowS
shows = showsPrec 0

showChar :: Char -> ShowS
showChar = (:)

showString :: String -> ShowS
showString = (++)

showParen :: Bool -> ShowS -> ShowS
showParen False sh = sh
showParen True  sh = \ x -> '(' : sh (')' : x)

showListWith :: forall a . (a -> ShowS) -> [a] -> ShowS
showListWith _  []     s = '[' : ']' : s
showListWith sh (x:xs) s = '[' : sh x (shl xs)
  where
    shl []     = ']' : s
    shl (y:ys) = ',' : sh y (shl ys)

appPrec :: Int
appPrec = 10
appPrec1 :: Int
appPrec1 = 11
