{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
module Transform.Simplify where

import qualified PlutusCore           as PLC
import           PlutusCore.MkPlc
import           PlutusCore.Pretty
import           UntypedPlutusCore

import qualified Data.ByteString.Lazy as BSL
import           Data.Coerce          (coerce)
import           Data.Text.Encoding   (encodeUtf8)
import           Test.Tasty
import           Test.Tasty.Golden

basic :: Term Name PLC.DefaultUni PLC.DefaultFun ()
basic = Force () $ Delay () $ mkConstant @Integer () 1

nested :: Term Name PLC.DefaultUni PLC.DefaultFun ()
nested = Force () $ Force () $ Delay () $ Delay () $ mkConstant @Integer () 1

extraDelays :: Term Name PLC.DefaultUni PLC.DefaultFun ()
extraDelays = Force () $ Delay () $ Delay () $ mkConstant @Integer () 1

interveningLambda :: Term Name PLC.DefaultUni PLC.DefaultFun ()
interveningLambda =
    let lam = LamAbs () (Name "" (coerce (1::Int))) $ Delay () $ mkConstant @Integer () 1
        arg = mkConstant @Integer () 1
    in Force () $ Apply () lam arg

-- TODO Fix duplication with other golden tests, quite annoying
goldenVsPretty :: PrettyPlc a => String -> String -> a -> TestTree
goldenVsPretty extn name value =
    goldenVsString name ("untyped-plutus-core/test/Transform/" ++ name ++ extn) $
        pure . BSL.fromStrict . encodeUtf8 . render $ prettyPlcClassicDebug value

goldenVsSimplified :: String -> Term Name PLC.DefaultUni PLC.DefaultFun () -> TestTree
goldenVsSimplified name
    = goldenVsPretty ".plc.golden" name
    . simplifyTerm

test_simplify :: TestTree
test_simplify =
    testGroup "simplify"
        [ goldenVsSimplified "basic" basic
        , goldenVsSimplified "nested" nested
        , goldenVsSimplified "extraDelays" extraDelays
        , goldenVsSimplified "interveningLambda" interveningLambda
        ]
