-- editorconfig-checker-disable-file
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}
module Transform.Simplify where

import PlutusCore qualified as PLC
import PlutusCore.MkPlc
import PlutusCore.Pretty
import PlutusCore.Quote
import UntypedPlutusCore

import Control.Lens ((&), (.~))
import Data.ByteString.Lazy qualified as BSL
import Data.Text.Encoding (encodeUtf8)
import Test.Tasty
import Test.Tasty.Golden

basic :: Term Name PLC.DefaultUni PLC.DefaultFun ()
basic = Force () $ Delay () $ mkConstant @Integer () 1

nested :: Term Name PLC.DefaultUni PLC.DefaultFun ()
nested = Force () $ Force () $ Delay () $ Delay () $ mkConstant @Integer () 1

extraDelays :: Term Name PLC.DefaultUni PLC.DefaultFun ()
extraDelays = Force () $ Delay () $ Delay () $ mkConstant @Integer () 1

interveningLambda :: Term Name PLC.DefaultUni PLC.DefaultFun ()
interveningLambda = runQuote $ do
    n <- freshName "a"
    let lam = LamAbs () n $ Delay () $ Apply () (Var () n) (Var () n)
        arg = mkConstant @Integer () 1
    pure $ Force () $ Apply () lam arg

basicInline :: Term Name PLC.DefaultUni PLC.DefaultFun ()
basicInline = runQuote $ do
    n <- freshName "a"
    pure $ Apply () (LamAbs () n (Var () n)) (mkConstant @Integer () 1)

mkInlinePurityTest ::
    Quote (Term Name PLC.DefaultUni PLC.DefaultFun ()) ->
    Term Name PLC.DefaultUni PLC.DefaultFun ()
mkInlinePurityTest termToInline = runQuote $ do
    a <- freshName "a"
    b <- freshName "b"
    Apply () (LamAbs () a $ LamAbs () b $ Var () a) <$> termToInline

inlinePure1 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
inlinePure1 = mkInlinePurityTest $ Var () <$> freshName "a"

inlinePure2 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
inlinePure2 = mkInlinePurityTest $ Force () . Delay () . Var () <$> freshName "a"

inlinePure3 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
inlinePure3 = mkInlinePurityTest $ do
    x <- freshName "x"
    y <- freshName "y"
    pure $
        Apply
            ()
            (LamAbs () x $ LamAbs () y $ Apply () (Var () x) (Var () x))
            (mkConstant @Integer () 1)

inlineImpure1 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
inlineImpure1 = mkInlinePurityTest $ pure $ Error ()

inlineImpure2 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
inlineImpure2 = mkInlinePurityTest $ pure . Force () . Delay () $ Error ()

inlineImpure3 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
inlineImpure3 = mkInlinePurityTest $ pure .
    Force () . Force () . Force () . Delay () . Delay () . Delay () $ Error ()

inlineImpure4 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
inlineImpure4 = mkInlinePurityTest $
    Force () . Force () . Force () . Delay () . Delay () . Var () <$> freshName "a"

multiApp :: Term Name PLC.DefaultUni PLC.DefaultFun ()
multiApp = runQuote $ do
    a <- freshName "a"
    b <- freshName "b"
    c <- freshName "c"
    let lam = LamAbs () a $ LamAbs () b $ LamAbs () c $ mkIterApp () (Var () c) [Var () a, Var () b]
        app = mkIterApp () lam [mkConstant @Integer () 1, mkConstant @Integer () 2, mkConstant @Integer () 3]
    pure app

-- TODO Fix duplication with other golden tests, quite annoying
goldenVsPretty :: PrettyPlc a => String -> String -> a -> TestTree
goldenVsPretty extn name value =
    goldenVsString name ("untyped-plutus-core/test/Transform/" ++ name ++ extn) $
        pure . BSL.fromStrict . encodeUtf8 . render $ prettyPlcClassicDebug value

goldenVsSimplified :: String -> Term Name PLC.DefaultUni PLC.DefaultFun () -> TestTree
goldenVsSimplified name
    = goldenVsPretty ".plc.golden" name
    . PLC.runQuote
    -- Just run one iteration, to see what that does
    . simplifyTerm (defaultSimplifyOpts & soMaxSimplifierIterations .~ 1)

test_simplify :: TestTree
test_simplify =
    testGroup "simplify"
        [ goldenVsSimplified "basic" basic
        , goldenVsSimplified "nested" nested
        , goldenVsSimplified "extraDelays" extraDelays
        , goldenVsSimplified "interveningLambda" interveningLambda
        , goldenVsSimplified "basicInline" basicInline
        , goldenVsSimplified "inlinePure1" inlinePure1
        , goldenVsSimplified "inlinePure2" inlinePure2
        , goldenVsSimplified "inlinePure3" inlinePure3
        , goldenVsSimplified "inlineImpure1" inlineImpure1
        , goldenVsSimplified "inlineImpure2" inlineImpure2
        , goldenVsSimplified "inlineImpure3" inlineImpure3
        , goldenVsSimplified "inlineImpure4" inlineImpure4
        , goldenVsSimplified "multiApp" multiApp
        ]
