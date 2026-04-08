{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NegativeLiterals #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:datatypes=BuiltinCasing #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}

module Unsupported.Spec where

import Test.Tasty.Extras

import Data.Proxy
import PlutusTx.Code
import PlutusTx.List qualified as List
import PlutusTx.Plugin
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
ord = plc (Proxy @"ord") (List.any (10 Prelude.>))

eq :: CompiledCode (Integer -> Integer -> Bool)
eq =
  plc
    (Proxy @"eq")
    ( \x y ->
        (x PlutusTx.+ y)
          Prelude.== (x PlutusTx.- y)
    )

io :: CompiledCode (Integer -> Integer -> Integer)
io =
  plc
    (Proxy @"io")
    ( \x y ->
        x
          PlutusTx.+ ( unsafePerformIO $ do
                         putStrLn "hello"
                         pure y
                     )
    )
