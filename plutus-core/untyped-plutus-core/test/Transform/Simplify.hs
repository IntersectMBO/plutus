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

caseOfCase1 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
caseOfCase1 = runQuote $ do
  b <- freshName "b"
  let ite = Force () (Builtin () PLC.IfThenElse)
      true = Constr () 0 []
      false = Constr () 1 []
      alts = [mkConstant @Integer () 1, mkConstant @Integer () 2]
  pure $ Case () (mkIterApp ite [((), Var () b), ((), true), ((), false)]) alts

{- | This should not simplify, because one of the branches of `ifThenElse` is not a `Constr`.
Unless both branches are known constructors, the case-of-case transformation
may increase the program size.
-}
caseOfCase2 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
caseOfCase2 = runQuote $ do
  b <- freshName "b"
  t <- freshName "t"
  let ite = Force () (Builtin () PLC.IfThenElse)
      true = Var () t
      false = Constr () 1 []
      alts = [mkConstant @Integer () 1, mkConstant @Integer () 2]
  pure $ Case () (mkIterApp ite [((), Var () b), ((), true), ((), false)]) alts

{- | Similar to `caseOfCase1`, but the type of the @true@ and @false@ branches is
@[Integer]@ rather than Bool (note that @Constr 0@ has two parameters, @x@ and @xs@).
-}
caseOfCase3 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
caseOfCase3 = runQuote $ do
  b <- freshName "b"
  x <- freshName "x"
  xs <- freshName "xs"
  f <- freshName "f"
  let ite = Force () (Builtin () PLC.IfThenElse)
      true = Constr () 0 [Var () x, Var () xs]
      false = Constr () 1 []
      altTrue = Var () f
      altFalse = mkConstant @Integer () 2
      alts = [altTrue, altFalse]
  pure $ Case () (mkIterApp ite [((), Var () b), ((), true), ((), false)]) alts

-- | The `Delay` should be floated into the lambda.
floatDelay1 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
floatDelay1 = runQuote $ do
  a <- freshName "a"
  let body = Apply () (Apply () (Builtin () PLC.AddInteger) (Force () (Var () a))) (Force () (Var () a))
      lam = LamAbs () a body
  pure $ Apply () lam (Delay () (mkConstant @Integer () 1))

{- | The `Delay` should not be floated into the lambda, because the argument (1 + 2)
is not work-free.
-}
floatDelay2 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
floatDelay2 = runQuote $ do
  a <- freshName "a"
  let body = Apply () (Apply () (Builtin () PLC.AddInteger) (Force () (Var () a))) (Force () (Var () a))
      lam = LamAbs () a body
      arg = Apply () (Apply () (Builtin () PLC.AddInteger) (mkConstant @Integer () 1)) (mkConstant @Integer () 2)
  pure $ Apply () lam (Delay () arg)

{- | The `Delay` should not be floated into the lambda in the first simplifier iteration,
because one of the occurrences of `a` is not under `Force`. It should be floated into
the lambda in the second simplifier iteration, after `b` is inlined.
-}
floatDelay3 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
floatDelay3 = runQuote $ do
  a <- freshName "a"
  b <- freshName "b"
  let secondArg = Force () (Apply () (LamAbs () b (Var () b)) (Var () a))
      body = Apply () (Apply () (Builtin () PLC.AddInteger) (Force () (Var () a))) secondArg
      lam = LamAbs () a body
  pure $ Apply () lam (Delay () (mkConstant @Integer () 1))

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
  -- In `[(\a . \b . a) termToInline]`, `termToInline` will be inlined
  -- if and only if it is pure.
  Apply () (LamAbs () a $ LamAbs () b $ Var () a) <$> termToInline

-- | A single @Var@ is pure.
inlinePure1 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
inlinePure1 = mkInlinePurityTest $ Var () <$> freshName "a"

{- | @force (delay a)@ is pure.

Note that this relies on @forceDelayCancel@ to cancel the @force@ and the @delay@,
otherwise the inliner would treat the term as impure.
-}
inlinePure2 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
inlinePure2 = mkInlinePurityTest $ Force () . Delay () . Var () <$> freshName "a"

{- | @[(\x -> \y -> [x x]) (con integer 1)]@ is pure.

Note that the @(con integer 1)@ won't get inlined: it isn't pre-inlined because
@x@ occurs twice, and it isn't post-inlined because @costIsAcceptable Constant{} = False@.
However, the entire term will be inlined since it is pure.
-}
inlinePure3 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
inlinePure3 = mkInlinePurityTest $ do
  x <- freshName "x"
  y <- freshName "y"
  pure $
    Apply
      ()
      (LamAbs () x $ LamAbs () y $ Apply () (Var () x) (Var () x))
      (mkConstant @Integer () 1)

{- | @force ([(\x -> delay (\y -> [x x])) (delay ([error (con integer 1)]))])@ is pure,
but it is very tricky to see so. It requires us to match up a force and a
delay through several steps of intervening computation.
-}
inlinePure4 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
inlinePure4 = mkInlinePurityTest $ do
  x <- freshName "x"
  y <- freshName "y"
  pure . Force () $
    Apply
      ()
      (LamAbs () x $ Delay () $ LamAbs () y $ Apply () (Var () x) (Var () x))
      (Delay () $ Apply () (Error ()) $ mkConstant @Integer () 1)

-- | @error@ is impure.
inlineImpure1 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
inlineImpure1 = mkInlinePurityTest $ pure $ Error ()

-- | @force (delay error)@ is impure.
inlineImpure2 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
inlineImpure2 = mkInlinePurityTest $ pure . Force () . Delay () $ Error ()

{- | @force (force (force (delay (delay (delay (error))))))@ is impure, since it
is the same as @error@.
-}
inlineImpure3 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
inlineImpure3 =
  mkInlinePurityTest
    $ pure
      . Force ()
      . Force ()
      . Force ()
      . Delay ()
      . Delay ()
      . Delay ()
    $ Error ()

{- | @force (force (force (delay (delay a))))@ is impure, since @a@ may expand
to an impure term such as @error@.
-}
inlineImpure4 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
inlineImpure4 =
  mkInlinePurityTest $
    Force () . Force () . Force () . Delay () . Delay () . Var () <$> freshName "a"

{- | @(\a -> f (a 0 1) (a 2)) (\x y -> g x y)@

The first occurrence of `a` should be inlined because doing so does not increase
the size or the cost.

The second occurrence of `a` should be unconditionally inlined in the second simplifier
iteration, but in this test we are only running one iteration.
-}
callsiteInline :: Term Name PLC.DefaultUni PLC.DefaultFun ()
callsiteInline = runQuote $ do
  a <- freshName "a"
  f <- freshName "f"
  g <- freshName "g"
  x <- freshName "x"
  y <- freshName "y"
  let fun =
        LamAbs () a $
          mkIterAppNoAnn
            (Var () f)
            [ mkIterAppNoAnn (Var () a) [mkConstant @Integer () 0, mkConstant @Integer () 1]
            , mkIterAppNoAnn (Var () a) [mkConstant @Integer () 2]
            ]
      arg = LamAbs () x . LamAbs () y $ mkIterAppNoAnn (Var () g) [Var () y, Var () x]
  pure $ Apply () fun arg

multiApp :: Term Name PLC.DefaultUni PLC.DefaultFun ()
multiApp = runQuote $ do
  a <- freshName "a"
  b <- freshName "b"
  c <- freshName "c"
  let lam = LamAbs () a $ LamAbs () b $ LamAbs () c $ mkIterAppNoAnn (Var () c) [Var () a, Var () b]
      app = mkIterAppNoAnn lam [mkConstant @Integer () 1, mkConstant @Integer () 2, mkConstant @Integer () 3]
  pure app

-- TODO Fix duplication with other golden tests, quite annoying
goldenVsPretty :: (PrettyPlc a) => String -> String -> a -> TestTree
goldenVsPretty extn name value =
  goldenVsString name ("untyped-plutus-core/test/Transform/" ++ name ++ extn) $
    pure . BSL.fromStrict . encodeUtf8 . render $
      prettyPlcClassicDebug value

goldenVsSimplified :: String -> Term Name PLC.DefaultUni PLC.DefaultFun () -> TestTree
goldenVsSimplified name =
  goldenVsPretty ".uplc.golden" name
    . PLC.runQuote
    -- Just run one iteration, to see what that does
    . simplifyTerm (defaultSimplifyOpts & soMaxSimplifierIterations .~ 1)

test_simplify :: TestTree
test_simplify =
  testGroup
    "simplify"
    [ goldenVsSimplified "basic" basic
    , goldenVsSimplified "nested" nested
    , goldenVsSimplified "extraDelays" extraDelays
    , goldenVsSimplified "caseOfCase1" caseOfCase1
    , goldenVsSimplified "caseOfCase2" caseOfCase2
    , goldenVsSimplified "caseOfCase3" caseOfCase3
    , goldenVsSimplified "floatDelay1" floatDelay1
    , goldenVsSimplified "floatDelay2" floatDelay2
    , goldenVsSimplified "floatDelay3" floatDelay3
    , goldenVsSimplified "interveningLambda" interveningLambda
    , goldenVsSimplified "basicInline" basicInline
    , goldenVsSimplified "callsiteInline" callsiteInline
    , goldenVsSimplified "inlinePure1" inlinePure1
    , goldenVsSimplified "inlinePure2" inlinePure2
    , goldenVsSimplified "inlinePure3" inlinePure3
    , goldenVsSimplified "inlinePure4" inlinePure4
    , goldenVsSimplified "inlineImpure1" inlineImpure1
    , goldenVsSimplified "inlineImpure2" inlineImpure2
    , goldenVsSimplified "inlineImpure3" inlineImpure3
    , goldenVsSimplified "inlineImpure4" inlineImpure4
    , goldenVsSimplified "multiApp" multiApp
    ]
