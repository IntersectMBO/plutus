{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:debug-context #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:profile-all #-}

module Plugin.Profiling where
import           Common
import           PlcTestUtils          (ToUPlc (toUPlc), goldenUEvalProfile)
import           Plugin.Lib            (MyExternalRecord (myExternal), andExternal, evenDirect)

import           Plugin.Data.Spec
import           Plugin.Functions.Spec hiding (recursiveFunctions)

import qualified PlutusTx.Builtins     as Builtins
import           PlutusTx.Code         (CompiledCode)
import           PlutusTx.Plugin       (plc)

import qualified PlutusCore.Default    as PLC

import           Data.Proxy
import           Data.Text             (Text)


profiling :: TestNested
profiling = testNested "Profiling" [
    recursiveFunctions
    , dataNewtypes
    -- , unfoldings
  ]

recursiveFunctions :: TestNested
recursiveFunctions = testNested "recursive" [
    -- goldenPir "fib" fib
     goldenUEvalProfile "fib4" [ toUPlc fib, toUPlc $ plc (Proxy @"4") (4::Integer) ]
    -- , goldenPir "sum" sumDirect
    , goldenUEvalProfile "sumList" [ toUPlc sumDirect, toUPlc listConstruct3 ]
    -- , goldenPir "even" evenMutual
    , goldenUEvalProfile "even3" [ toUPlc evenMutual, toUPlc $ plc (Proxy @"3") (3::Integer) ]
    , goldenUEvalProfile "even4" [ toUPlc evenMutual, toUPlc $ plc (Proxy @"4") (4::Integer) ]
      ]

dataNewtypes :: TestNested
dataNewtypes = testNested "data, newtypes" [
    goldenUEvalProfile "ptreeConstDest" [ toUPlc ptreeMatch, toUPlc ptreeConstruct ]
    , goldenUEvalProfile "polyRecEval" [ toUPlc polyRec, toUPlc ptreeConstruct ]
    , goldenUEvalProfile "ptreeFirstEval" [ toUPlc ptreeFirst, toUPlc ptreeConstruct ]
    , goldenUEvalProfile "sameEmptyRoseEval" [ toUPlc sameEmptyRose, toUPlc emptyRoseConstruct ]
    ]
