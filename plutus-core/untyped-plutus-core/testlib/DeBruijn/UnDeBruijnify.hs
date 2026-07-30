{-# LANGUAGE TypeApplications #-}

{-| The point of these tests is that binders with wrong indices will be undebruijnified
successfully, whereas variables with wrong indices (e.g. out of scope) will fail. -}
module DeBruijn.UnDeBruijnify (test_undebruijnify) where

import PlutusCore qualified as PLC
import PlutusCore.Default
import PlutusCore.Error
import PlutusCore.MkPlc
import PlutusCore.Pretty
import PlutusCore.Quote
import PlutusCore.StdLib.Data.Bool
import UntypedPlutusCore as UPLC
import UntypedPlutusCore.Test.DeBruijn.Bad
import UntypedPlutusCore.Test.DeBruijn.Good

import Control.Monad.Except
import Control.Monad.State
import Test.Tasty.Extras

type T = Term DeBruijn DefaultUni DefaultFun ()

-- | (lam0 [2 1 4 (lam1 [1 4 3 5])])
graceElaborate :: T
graceElaborate =
  lamAbs0 $
    v 2
      @@ [ v 1
         , v 4
         , lamAbs1 $
             v 1
               @@ [ v 4
                  , v 3
                  , v 5
                  ]
         ]
  where
    v = Var () . DeBruijn

testsDefault :: [(String, T)]
testsDefault =
  [ ("okId0", idFun0)
  , ("okId99", fun1var1)
  , ("okConst", const0 @@ [true, fun1var1])
  , ("okDeep0", deepFun0 10)
  , ("okDeep99", deepFun1 10)
  , ("okMix1", deepMix0_1 10)
  , ("okMix2", deepMix1_0 10)
  , ("failTop", Delay () var0)
  , ("failDeep", deepOut0 10)
  , ("failBody0", fun0var0)
  , ("failBody99", fun1var0)
  , ("failConst", const0 @@ [true, fun0var0])
  , ("failITE", ite10)
  , ("failMix", deepOutMix1_0 10)
  , ("failTop0", var0)
  , ("failTop1", Var () $ DeBruijn 1)
  , ("failApply01", manyFree01)
  ]

{-| This is testing the (non-default) behavior of undebruijnification where
free debruijn indices are gracefully (without throwing an error) converted to fresh uniques.
See `freeIndexAsConsistentLevel` -}
testsGrace :: [(String, T)]
testsGrace =
  [ ("graceTop", Delay () var0)
  , ("graceDeep", deepOut0 5)
  , ("graceConst", const0 @@ [true, fun0var0])
  , ("graceElaborate", graceElaborate)
  ]

test_undebruijnify :: TestNested
test_undebruijnify =
  testNested
    "Golden"
    [ testNested "Default" $
        fmap (nestedGoldenVsPretty actDefault) testsDefault
    , testNested "Graceful" $
        fmap (nestedGoldenVsPretty actGrace) testsGrace
    ]
  where
    nestedGoldenVsPretty act (n, t) =
      nestedGoldenVsDoc n ".uplc" $ toPretty $ act $ mkProg t

    actDefault = progTerm $ modifyError FreeVariableErrorE . unDeBruijnTerm

    actGrace =
      flip evalStateT mempty
        . progTerm (unDeBruijnTermWith freeIndexAsConsistentLevel)

    mkProg = Program () PLC.latestVersion . termMapNames fakeNameDeBruijn

    toPretty = prettyPlcClassicSimple . runExcept @(Error DefaultUni DefaultFun ()) . runQuoteT
