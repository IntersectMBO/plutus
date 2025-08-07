{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE BlockArguments      #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-cse-iterations=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-pir=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-uplc=0 #-}

{-# HLINT ignore "Eta reduce" #-}
{-# HLINT ignore "Redundant if" #-}

module Main where

import PlutusCore.Pretty
import PlutusCore.Test (goldenUEval)
import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Code (CompiledCode, getPir)
import PlutusTx.Prelude qualified as P
import PlutusTx.Test (goldenPirReadable, goldenUPlc)
import PlutusTx.TH

import PlutusTx.Builtins qualified as BI

import Data.Proxy (Proxy (..))
import Test.Tasty.Extras (TestNested, testNested, testNestedGhc)

main :: IO ()
main = do
  print $ pretty $ getPir bar
  -- print $ pretty $ getPir foo

-- foo :: CompiledCode (Integer -> Bool)
-- foo = $$(compile [||\(x :: Integer) -> BI.caseInteger x [True, False, True]||])

-- caseInteger :: Integer -> [a] -> a
-- caseInteger 0 (x:_) = x
-- caseInteger n (_:xs) =
--   if n > 0
--   then caseInteger (n-1) xs
--   else BI.error ()
-- caseInteger _ _ = BI.error ()

myFunc :: Bool -> Integer -> Integer
myFunc False _ = 1
myFunc True i =  go i
  where
    go = \case
      1 -> 2
      2 -> 123
      3 -> 15123
      4 -> 1111
      5 -> 4
      _ -> BI.error ()

aaa :: Integer -> Integer
aaa i = BI.caseInteger i [0, 1, 2, 3, 4, 5]

bar :: CompiledCode (Integer -> Integer)
bar = $$(compile [||aaa||])
