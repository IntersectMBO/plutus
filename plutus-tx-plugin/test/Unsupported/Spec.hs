{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NegativeLiterals #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fplugin Plinth.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:datatypes=BuiltinCasing #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:defer-errors #-}

module Unsupported.Spec where

import Test.Tasty.Extras

import Plinth.Plugin
import PlutusTx.Code
import PlutusTx.List qualified as List
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Test
import System.IO.Unsafe

tests :: TestNested
tests =
  testNested "Unsupported" . pure $
    testNestedGhc
      [ goldenUPlcReadable "ord" ord
      , goldenUPlcReadable "eq" eq
      , goldenUPlcReadable "io" io
      ]

ord :: CompiledCode ([Integer] -> Bool)
ord = plinthc (List.any (10 Prelude.>))

eq :: CompiledCode (Integer -> Integer -> Bool)
eq =
  plinthc
    ( \x y ->
        (x PlutusTx.+ y)
          Prelude.== (x PlutusTx.- y)
    )

io :: CompiledCode (Integer -> Integer -> Integer)
io =
  plinthc
    ( \x y ->
        x
          PlutusTx.+ ( unsafePerformIO $ do
                         putStrLn "hello"
                         pure y
                     )
    )
