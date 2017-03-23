{-# OPTIONS -Wall #-}







module Utils.JSABT where

import Data.List (intercalate)







data JSABT = JSABT { constructor :: String, args :: [JSABT] }
           | JSInt Int
           | JSFloat Float
           | JSString String
           | JSVar String
           | JSScope [String] JSABT
           | JSArray [JSABT]

class ToJS a where
  toJS :: a -> JSABT

jsABTToSource :: JSABT -> String
jsABTToSource (JSABT c ms) =
  "{ constructor: " ++ show c ++ ", args: " ++ jsABTToSource (JSArray ms) ++ " }"
jsABTToSource (JSInt i) =
  show i
jsABTToSource (JSFloat f) =
  show f
jsABTToSource (JSString s) =
  show s
jsABTToSource (JSVar x) =
  x
jsABTToSource (JSScope xs b) =
  "function (" ++ intercalate "," xs ++ ") { return " ++ jsABTToSource b ++ "; }"
jsABTToSource (JSArray ms) =
  "[" ++ intercalate "," (map jsABTToSource ms) ++ "]"