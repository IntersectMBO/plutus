{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-omit-interface-pragmas #-}
{-# OPTIONS_GHC -fplugin PlutusTx.Plugin -fplugin-opt PlutusTx.Plugin:defer-errors -fplugin-opt PlutusTx.Plugin:no-context #-}

module Plugin.Optimization.Spec where

import           Common          (TestNested, testNested)
import           Data.Proxy      (Proxy (..))
import           Lib             (goldenPir)
import           PlutusTx.Code   (CompiledCode)
import           PlutusTx.Plugin (plc)

optimization :: TestNested
optimization = testNested "Optimization" [
    removeUnusedConstrs
  ]

-- FIXME: Add many more tests
removeUnusedConstrs :: TestNested
removeUnusedConstrs = testNested "removeUnusedConstrs" [
    goldenPir "unusedConstrsConst" unusedConstrsConst,
    goldenPir "unusedConstrsMatchConst" unusedConstrsMatchConst,
    goldenPir "unusedConstrsMatchFuncConst" unusedConstrsMatchFuncConst,
    goldenPir "unusedConstrsMatchFunc" unusedConstrsMatchFunc
  ]

unusedConstrsConst :: CompiledCode (Maybe Integer)
unusedConstrsConst = plc (Proxy @"unusedConstrsConst") (Just 1)

unusedConstrsMatchConst :: CompiledCode (Maybe Integer)
unusedConstrsMatchConst = plc (Proxy @"unusedConstrsMatchConst")
                              (case Just 1 of { Just y -> Just y; _ -> Just 0 })

unusedConstrsMatchFuncConst :: CompiledCode (Maybe Integer)
unusedConstrsMatchFuncConst = plc (Proxy @"unusedConstrsMatchFuncConst")
                                  ((\x -> case x of { Just y -> Just y; _ -> Just 0 }) (Just 1))

unusedConstrsMatchFunc :: CompiledCode (Maybe Integer -> Integer)
unusedConstrsMatchFunc = plc (Proxy @"unusedConstrsMatchFunc")
                             ((\x -> case x of { Just y -> y; _ -> 0 }))
