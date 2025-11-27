{-# LANGUAGE TypeApplications #-}

{-| The point of these tests is that *both* binders with wrong indices and
variables with wrong indices (e.g. out of scope) will fail the scope-check pass. -}
module DeBruijn.Scope (test_scope) where

import PlutusCore.Default
import PlutusCore.MkPlc
import PlutusCore.StdLib.Data.Unit
import PlutusPrelude
import UntypedPlutusCore
import UntypedPlutusCore.Test.DeBruijn.Bad
import UntypedPlutusCore.Test.DeBruijn.Good

import Control.Monad.Except
import Test.Tasty.Extras
import Test.Tasty.HUnit

type T = Term DeBruijn DefaultUni DefaultFun ()

testsOk :: [(String, T)]
testsOk =
  [ ("idFun0", idFun0)
  , ("deepFun0", deepFun0 10)
  , ("deeperFun0", deeperFun0 10)
  ]

testsFail :: [(String, T)]
testsFail =
  [ ("delay0", Delay () var0)
  , ("top0", var0)
  , ("top1", Var () $ DeBruijn 1)
  , ("fun1var1", fun1var1)
  , ("fun0var0", fun0var0)
  , ("fun1var0", fun1var0)
  , ("const0var0", const0 @@ [unitval, fun0var0])
  , ("const0var1", const0 @@ [unitval, fun1var1])
  , ("ite10", ite10)
  , ("deepOut0", deepOut0 10)
  , ("deepFun1", deepFun1 10)
  , ("deepMix0_1", deepMix0_1 10)
  , ("deepOutMix1_0", deepOutMix1_0 10)
  , ("manyFree01", manyFree01)
  ]

test_scope :: TestNested
test_scope =
  testNested "Scope" $
    embed . uncurry testCase
      <$> (second testPasses <$> testsOk)
        <> (second testThrows <$> testsFail)
  where
    testPasses t = isRight (runScope t) @? "scope checking failed unexpectedly"

    testThrows t = isLeft (runScope t) @? "scope checking passed unexpectedly"

    runScope = runExcept @FreeVariableError . checkScope
