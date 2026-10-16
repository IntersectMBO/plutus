module PlutusTx.Plugin.Deriving.Constant.Module
  ( controlApplicative
  , controlLens
  , dataAeson
  , dataHashMapStrictInsOrd
  , dataMaybe
  , dataMonoid
  , dataProxy
  , dataString
  , dataSwagger
  , plutusTx
  , plutusTxBuiltins
  , testQuickCheck
  )
where

import GHC.Unit.Module qualified as Ghc

controlApplicative :: Ghc.ModuleName
controlApplicative = Ghc.mkModuleName "Control.Applicative"

controlLens :: Ghc.ModuleName
controlLens = Ghc.mkModuleName "Control.Lens"

dataAeson :: Ghc.ModuleName
dataAeson = Ghc.mkModuleName "Data.Aeson"

dataHashMapStrictInsOrd :: Ghc.ModuleName
dataHashMapStrictInsOrd = Ghc.mkModuleName "Data.HashMap.Strict.InsOrd"

dataMaybe :: Ghc.ModuleName
dataMaybe = Ghc.mkModuleName "Data.Maybe"

dataMonoid :: Ghc.ModuleName
dataMonoid = Ghc.mkModuleName "Data.Monoid"

dataProxy :: Ghc.ModuleName
dataProxy = Ghc.mkModuleName "Data.Proxy"

dataString :: Ghc.ModuleName
dataString = Ghc.mkModuleName "Data.String"

dataSwagger :: Ghc.ModuleName
dataSwagger = Ghc.mkModuleName "Data.Swagger"

plutusTx :: Ghc.ModuleName
plutusTx = Ghc.mkModuleName "PlutusTx"

plutusTxBuiltins :: Ghc.ModuleName
plutusTxBuiltins = Ghc.mkModuleName "PlutusTx.Builtins"

testQuickCheck :: Ghc.ModuleName
testQuickCheck = Ghc.mkModuleName "Test.QuickCheck"
