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

import PlutusTx.Test (EvalResult, applyLifted, evaluateCompiledCode, prettyEvalResult)

-- BEGIN Plinth
plinthCode :: Integer -> Integer
plinthCode x = trace "Evaluating x" x + trace "Evaluating constant" 2

compiledCode :: CompiledCode (Integer -> Integer)
compiledCode = plc (Proxy @"plinth") plinthCode
-- END Plinth

{-
EvalResult
    { evalResult = Right
        ( Constant ()
            ( Some
                ( ValueOf DefaultUniInteger 4 )
            )
        )
    , evalResultBudget = ExBudget
        { exBudgetCPU = ExCPU 508304
        , exBudgetMemory = ExMemory 1966
        }
    , evalResultTraces =
        [ "Evaluating x"
        , "Evaluating constant"
        ]
    }
-}

-- BEGIN AppliedResult
result :: EvalResult
result = evaluateCompiledCode $ compiledCode `applyLifted` 2
-- END AppliedResult

-- BEGIN main
main :: IO ()
main = Text.putStrLn $ prettyEvalResult result
-- END main
