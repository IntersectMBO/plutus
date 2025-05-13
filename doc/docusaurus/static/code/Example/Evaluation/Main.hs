{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:target-version=1.1.0 #-}

module Main where

import PlutusTx.Prelude

import Data.Text.IO qualified as Text
import PlutusTx (CompiledCode, applyCode, compile, liftCodeDef, unsafeApplyCode)
import Prelude (IO, String)

import PlutusTx.Test (EvalResult, displayEvalResult, evaluateCompiledCode)

-- BEGIN Plinth

plinthCode :: Integer -> Integer
plinthCode x = trace "Evaluating x" x + trace "Evaluating constant" 2

-- END Plinth

-- BEGIN CompiledCode

compiledCode :: CompiledCode (Integer -> Integer)
compiledCode = $$(compile [||plinthCode||])

-- END CompiledCode

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

-- BEGIN CompiledArgument

argumentCompiled :: CompiledCode Integer
argumentCompiled = $$(compile [||2||])

-- END CompiledArgument

-- BEGIN LiftedArgument

argumentLifted :: CompiledCode Integer
argumentLifted = liftCodeDef 2

-- END LiftedArgument

-- BEGIN SafeApplicationResult

errorOrResult :: Either String EvalResult
errorOrResult = fmap evaluateCompiledCode appliedSafely
 where
  appliedSafely :: Either String (CompiledCode Integer)
  appliedSafely = compiledCode `applyCode` argumentLifted

-- END SafeApplicationResult

-- BEGIN UnsafeApplicationResult

result :: EvalResult
result = evaluateCompiledCode appliedUnsafely
 where
  appliedUnsafely :: CompiledCode Integer
  appliedUnsafely = compiledCode `unsafeApplyCode` argumentCompiled

-- END UnsafeApplicationResult

-- BEGIN main

main :: IO ()
main = Text.putStrLn $ displayEvalResult result

-- END main
