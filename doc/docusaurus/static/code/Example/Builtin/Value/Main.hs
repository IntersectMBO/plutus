{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fplugin Plinth.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt Plinth.Plugin:target-version=1.1.0 #-}

module Main where

import Control.Monad (unless)
import Data.ByteString (ByteString)
import Data.Text.IO qualified as Text
import PlutusCore.Data (Data (B, I, Map))
import PlutusCore.Version (plcVersion110)
import PlutusTx qualified as Plinth
import PlutusTx.Builtins
  ( BuiltinByteString
  , BuiltinData
  , assetCount
  , dataToBuiltinData
  , keepPolicies
  , toOpaque
  , unsafeDataAsValue
  , valueContains
  )
import PlutusTx.Eval
  ( displayEvalResult
  , evaluateCompiledCode
  , evaluatesToError
  , evaluatesWithoutError
  )
import PlutusTx.Prelude qualified as P
import System.Exit (exitFailure)

--------------------------------------------------------------------------------
-- Plinth ----------------------------------------------------------------------

{-| Accepts an output that still holds every token the input holds under the
protocol's policy, and that holds at most ten distinct assets. Fails otherwise. -}
checkOutput :: BuiltinByteString -> BuiltinData -> BuiltinData -> P.BuiltinUnit
checkOutput protocol inputValue outputValue =
  P.check
    ( valueContains output (keepPolicies (toOpaque [protocol]) input)
        P.&& (assetCount output P.<= 10)
    )
  where
    input = unsafeDataAsValue inputValue
    output = unsafeDataAsValue outputValue
{-# INLINEABLE checkOutput #-}

compiledCheckOutput
  :: Plinth.CompiledCode (BuiltinByteString -> BuiltinData -> BuiltinData -> P.BuiltinUnit)
compiledCheckOutput = $$(Plinth.compile [||checkOutput||])

--------------------------------------------------------------------------------
-- Main ------------------------------------------------------------------------

main :: IO ()
main = do
  let input =
        value
          [ ("", [("", 5000000)])
          , ("other", [("coin", 7)])
          , ("protocol", [("state", 1)])
          ]
      keepsState = check input (value [("", [("", 2000000)]), ("protocol", [("state", 1)])])
      dropsState = check input (value [("", [("", 2000000)]), ("other", [("coin", 7)])])
  Text.putStrLn . displayEvalResult . evaluateCompiledCode $ keepsState
  Text.putStrLn . displayEvalResult . evaluateCompiledCode $ dropsState
  unless (evaluatesWithoutError keepsState && evaluatesToError dropsState) exitFailure
  where
    check input output =
      compiledCheckOutput
        `Plinth.unsafeApplyCode` Plinth.liftCode plcVersion110 "protocol"
        `Plinth.unsafeApplyCode` Plinth.liftCode plcVersion110 (dataToBuiltinData input)
        `Plinth.unsafeApplyCode` Plinth.liftCode plcVersion110 (dataToBuiltinData output)

{-| The `Data` encoding of a value, as found in a script context. Currency
symbols and token names must be listed in ascending order. -}
value :: [(ByteString, [(ByteString, Integer)])] -> Data
value currencies =
  Map
    [ (B currency, Map [(B token, I amount) | (token, amount) <- tokens])
    | (currency, tokens) <- currencies
    ]
