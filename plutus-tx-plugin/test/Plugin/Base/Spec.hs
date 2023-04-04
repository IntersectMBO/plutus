{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# OPTIONS_GHC -fno-enable-builtin-rules #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:context-level=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:defer-errors #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-pir=0 #-}
{-# OPTIONS_GHC -fplugin-opt PlutusTx.Plugin:max-simplifier-iterations-uplc=0 #-}

module Plugin.Base.Spec where

import Test.Tasty.Extras

import PlutusTx.Code
import PlutusTx.Prelude qualified as PlutusTx
import PlutusTx.Test
import PlutusTx.TH (compile)

base :: TestNested
base =
    testNested
        "Base"
        [ goldenPir "matchInteger" matchInteger
        -- TODO: `listRangeSyntax` doesn't yet work; it requires adding
        -- `enumFromTo @Integer` to `knownApps.
        -- , goldenPir "listRangeSyntax" listRangeSyntax
        ]

matchInteger :: CompiledCode (Integer -> Integer)
matchInteger =
    $$( compile
            [||
            (\(x :: Integer) -> case x + 1 of 3 -> 42; _ -> 43)
            ||]
      )

listRangeSyntax :: CompiledCode Bool
listRangeSyntax =
    $$( compile
            [||
            let ls = [1 .. 10] :: [Integer]
             in PlutusTx.any (10 >) ls
            ||]
      )
