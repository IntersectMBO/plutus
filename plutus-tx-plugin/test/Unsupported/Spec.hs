{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NegativeLiterals #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fplugin Plinth.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:defer-errors #-}

module Unsupported.Spec where

import Test.Tasty.Extras

import Data.ByteString qualified as BS
import Data.Text qualified as Text
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
      , goldenUPlcReadable "dbl" dbl
      , goldenUPlcReadable "text" text
      , goldenUPlcReadable "bytestring" bytestring
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

dbl :: CompiledCode (Double -> Double)
dbl = plinthc (\x -> x)

text :: CompiledCode (Text.Text -> Text.Text)
text = plinthc (\x -> x)

bytestring :: CompiledCode (BS.ByteString -> BS.ByteString)
bytestring = plinthc (\x -> x)

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
