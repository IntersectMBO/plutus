{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:target-version=1.1.0 #-}

module Main where

import Data.Proxy (Proxy (..))
import Data.Text.IO qualified as Text
import PlutusTx
import PlutusTx.Plugin (plc)
import PlutusTx.Prelude
import Prelude (IO)

import PlutusTx.Test (CodeResult, applyLifted, evaluateCompiledCode, prettyCodeResult)

-- BEGIN Plinth
plinthCode :: Integer -> Integer
plinthCode x = trace "Evaluating x" x + trace "Evaluating constant" 2

compiledCode :: CompiledCode (Integer -> Integer)
compiledCode = plc (Proxy @"plinth") plinthCode
-- END Plinth

{-
CodeResult
    { codeResult = Right
        ( Constant ()
            ( Some
                ( ValueOf DefaultUniInteger 4 )
            )
        )
    , codeBudget = ExBudget
        { exBudgetCPU = ExCPU 508304
        , exBudgetMemory = ExMemory 1966
        }
    , codeTraces =
        [ "Evaluating x"
        , "Evaluating constant"
        ]
    }
-}

-- BEGIN AppliedResult
result :: CodeResult
result = evaluateCompiledCode $ compiledCode `applyLifted` 2
-- END AppliedResult

-- BEGIN main
main :: IO ()
main = Text.putStrLn $ prettyCodeResult result
-- END main
