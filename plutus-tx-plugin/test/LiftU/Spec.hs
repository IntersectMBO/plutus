-- editorconfig-checker-disable-file
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NegativeLiterals      #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# OPTIONS_GHC   -Wno-orphans #-}
module LiftU.Spec where

import PlutusTx.LiftU

import Prelude

import Plugin.Data.Spec
import Plugin.Primitives.Spec

import PlutusCore qualified as PLC
import PlutusCore.Test
import PlutusTx.Builtins qualified as Builtins
import PlutusTx.Builtins.Class
import PlutusTx.Code
import PlutusTx.Test ()

import Data.Proxy
import Hedgehog
import Hedgehog.Gen as Gen
import Hedgehog.Range
import Test.Tasty
import Test.Tasty.Hedgehog

trippingTests :: TestTree
trippingTests = testGroup "unliftU . liftU == id"
  [ test_liftUTripping "Integer" (fmap toBuiltin $ integral (linear @Integer -100 100))
  , test_liftUTripping "Bool" (enumBounded @_ @Bool)
  , test_liftUTripping "Maybe Integer" (Gen.maybe $ fmap toBuiltin $ integral (linear @Integer -100 100))
  , test_liftUTripping "List Integer" (Gen.list (linear 0 50) $ fmap toBuiltin $ integral (linear @Integer -100 100))
  ]

test_liftUTripping :: (LiftU PLC.Name PLC.DefaultUni PLC.DefaultFun a, UnliftU PLC.Name PLC.DefaultUni PLC.DefaultFun a, Show a, Eq a) => String -> Gen a -> TestTree
test_liftUTripping n g = testProperty n $
  prop_liftUTripping (Proxy :: Proxy PLC.Name) (Proxy :: Proxy PLC.DefaultUni) (Proxy :: Proxy PLC.DefaultFun) g

prop_liftUTripping
  :: forall name uni fun a
  . (LiftU name uni fun a, UnliftU name uni fun a, Show a, Eq a, PLC.GShow uni, PLC.Closed uni, uni `PLC.Everywhere` Show, Show name, Show fun)
  => Proxy name
  -> Proxy uni
  -> Proxy fun
  -> Gen a
  -> Property
prop_liftUTripping _ _ _ g = property $ do
  a <- forAll g
  tripping a (liftU @name @uni @fun @a) (unliftU @name @uni @fun @a)

defaultMakeLiftU ''MyMonoData
defaultMakeLiftU ''MyMonoRecord
defaultMakeLiftU ''MyPolyData

data NestedRecord = NestedRecord { unNested :: Maybe (Integer, Integer) }
defaultMakeLiftU ''NestedRecord

data WrappedBS = WrappedBS { unWrap :: Builtins.BuiltinByteString }
defaultMakeLiftU ''WrappedBS

newtype NewtypeInt = NewtypeInt { unNt :: Integer }
defaultMakeLiftU ''NewtypeInt

newtype Newtype2 = Newtype2 { unNt2 :: NewtypeInt }
defaultMakeLiftU ''Newtype2

newtype Newtype3 = Newtype3 { unNt3 :: Newtype2 }
defaultMakeLiftU ''Newtype3

-- 'Z' so it sorts late and this doesn't work by accident
data Z = Z Integer
defaultMakeLiftU ''Z
type Syn = Z

data SynExample = SynExample { unSE :: Syn }
defaultMakeLiftU ''SynExample

tests :: TestNested
tests = testNested "LiftU" [
    goldenUPlc "int" (liftProgramDef (1::Integer))
    , goldenUPlc "tuple" (liftProgramDef (1::Integer, 2::Integer))
    , goldenUPlc "mono" (liftProgramDef (Mono2 2))
    , goldenUEval "monoInterop" [ getPlc monoCase, liftProgramDef (Mono1 1 2) ]
    , goldenUPlc "poly" (liftProgramDef (Poly1 (1::Integer) (2::Integer)))
    , goldenUEval "polyInterop" [ getPlc defaultCasePoly, liftProgramDef (Poly1 (1::Integer) (2::Integer)) ]
    , goldenUPlc "record" (liftProgramDef (MyMonoRecord 1 2))
    , goldenUEval "boolInterop" [ getPlc andPlc, liftProgramDef True, liftProgramDef True ]
    , goldenUPlc "list" (liftProgramDef ([1]::[Integer]))
    , goldenUEval "listInterop" [ getPlc listMatch, liftProgramDef ([1]::[Integer]) ]
    , goldenUPlc "nested" (liftProgramDef (NestedRecord (Just (1, 2))))
    , goldenUPlc "bytestring" (liftProgramDef (WrappedBS "hello"))
    , goldenUPlc "newtypeInt" (liftProgramDef (NewtypeInt 1))
    , goldenUPlc "newtypeInt2" (liftProgramDef (Newtype2 $ NewtypeInt 1))
    , goldenUPlc "newtypeInt3" (liftProgramDef (Newtype3 $ Newtype2 $ NewtypeInt 1))
    , goldenUPlc "syn" (liftProgramDef (SynExample $ Z $ 1))
 ]
