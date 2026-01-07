{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Transform.Simplify.Spec where

import Data.Text (Text)
import Data.Vector qualified as V
import PlutusCore qualified as PLC
import PlutusCore.MkPlc (mkConstant, mkIterApp, mkIterAppNoAnn)
import PlutusCore.Quote (Quote, freshName, runQuote)
import Test.Tasty (TestTree, testGroup)
import Transform.Simplify.Lib (goldenVsCse, goldenVsSimplified)
import UntypedPlutusCore
  ( CseWhichSubterms (..)
  , DefaultFun
  , DefaultUni
  , Name
  , Term (..)
  , UVarDecl (..)
  )
import UntypedPlutusCore.MkUPlc (mkIterLamAbs)

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
      alts = V.fromList [mkConstant @Integer () 1, mkConstant @Integer () 2]
  pure $ Case () (mkIterApp ite [((), Var () b), ((), true), ((), false)]) alts

{-| This should not simplify, because one of the branches of `ifThenElse` is not a `Constr`.
Unless both branches are known constructors, the case-of-case transformation
may increase the program size. -}
caseOfCase2 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
caseOfCase2 = runQuote $ do
  b <- freshName "b"
  t <- freshName "t"
  let ite = Force () (Builtin () PLC.IfThenElse)
      true = Var () t
      false = Constr () 1 []
      alts = V.fromList [mkConstant @Integer () 1, mkConstant @Integer () 2]
  pure $ Case () (mkIterApp ite [((), Var () b), ((), true), ((), false)]) alts

{-| Similar to `caseOfCase1`, but the type of the @true@ and @false@ branches is
@[Integer]@ rather than Bool (note that @Constr 0@ has two parameters, @x@ and @xs@). -}
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
      alts = V.fromList [altTrue, altFalse]
  pure $ Case () (mkIterApp ite [((), Var () b), ((), true), ((), false)]) alts

-- | The `Delay` should be floated into the lambda.
floatDelay1 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
floatDelay1 = runQuote $ do
  a <- freshName "a"
  let body =
        Apply
          ()
          (Apply () (Builtin () PLC.AddInteger) (Force () (Var () a)))
          (Force () (Var () a))
      lam = LamAbs () a body
  pure $ Apply () lam (Delay () (mkConstant @Integer () 1))

{-| The `Delay` should not be floated into the lambda, because the argument (1 + 2)
is not work-free. -}
floatDelay2 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
floatDelay2 = runQuote $ do
  a <- freshName "a"
  let body =
        Apply
          ()
          (Apply () (Builtin () PLC.AddInteger) (Force () (Var () a)))
          (Force () (Var () a))
      lam = LamAbs () a body
      arg =
        Apply
          ()
          (Apply () (Builtin () PLC.AddInteger) (mkConstant @Integer () 1))
          (mkConstant @Integer () 2)
  pure $ Apply () lam (Delay () arg)

{-| The `Delay` should not be floated into the lambda in the first simplifier iteration,
because one of the occurrences of `a` is not under `Force`. It should be floated into
the lambda in the second simplifier iteration, after `b` is inlined. -}
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

{-| A helper function to create a term which tests whether the inliner
behaves as expected for a given pure or impure term. It receives
a 'Quote' that produces a term together with a list of free variables.
The free variables are bound at the top level of the final term in order
to ensure that the produced final term is well-scoped. -}
mkInlinePurityTest
  :: Quote ([Name], Term Name PLC.DefaultUni PLC.DefaultFun ())
  -> Term Name PLC.DefaultUni PLC.DefaultFun ()
mkInlinePurityTest termToInline = runQuote $ do
  a <- freshName "a"
  b <- freshName "b"
  -- In `[(\a . \b . a) termToInline]`, `termToInline` will be inlined
  -- if and only if it is pure.
  (freeVars, term) <- termToInline
  let withTopLevelBindings =
        mkIterLamAbs
          (UVarDecl () <$> freeVars)
  pure $
    withTopLevelBindings $
      Apply () (LamAbs () a $ LamAbs () b $ Var () a) term

-- | A single @Var@ is pure.
inlinePure1 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
inlinePure1 = mkInlinePurityTest $ do
  a <- freshName "a"
  pure ([a], Var () a)

{-| @force (delay a)@ is pure.

Note that this relies on @forceDelayCancel@ to cancel the @force@ and the @delay@,
otherwise the inliner would treat the term as impure. -}
inlinePure2 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
inlinePure2 = mkInlinePurityTest $ do
  a <- freshName "a"
  pure ([a], Force () $ Delay () $ Var () a)

{-| @[(\x -> \y -> [x x]) (con integer 1)]@ is pure.

Note that the @(con integer 1)@ won't get inlined: it isn't pre-inlined because
@x@ occurs twice, and it isn't post-inlined because @costIsAcceptable Constant{} = False@.
However, the entire term will be inlined since it is pure. -}
inlinePure3 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
inlinePure3 = mkInlinePurityTest $ do
  x <- freshName "x"
  y <- freshName "y"
  let t =
        Apply
          ()
          (LamAbs () x $ LamAbs () y $ Apply () (Var () x) (Var () x))
          (mkConstant @Integer () 1)
      vars = []
  pure (vars, t)

{-| @force ([(\x -> delay (\y -> [x x])) (delay ([error (con integer 1)]))])@ is pure,
but it is very tricky to see so. It requires us to match up a force and a
delay through several steps of intervening computation. -}
inlinePure4 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
inlinePure4 = mkInlinePurityTest $ do
  x <- freshName "x"
  y <- freshName "y"
  let term =
        Force () $
          Apply
            ()
            (LamAbs () x $ Delay () $ LamAbs () y $ Apply () (Var () x) (Var () x))
            (Delay () $ Apply () (Error ()) $ mkConstant @Integer () 1)
  pure ([], term)

-- | @error@ is impure.
inlineImpure1 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
inlineImpure1 = mkInlinePurityTest $ pure ([], Error ())

-- | @force (delay error)@ is impure.
inlineImpure2 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
inlineImpure2 = mkInlinePurityTest $ pure ([], Force () . Delay () $ Error ())

{-| @force (force (force (delay (delay (delay (error))))))@ is impure, since it
is the same as @error@. -}
inlineImpure3 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
inlineImpure3 =
  mkInlinePurityTest $
    pure
      ( []
      , Force ()
          . Force ()
          . Force ()
          . Delay ()
          . Delay ()
          . Delay ()
          $ Error ()
      )

{-| @force (force (force (delay (delay a))))@ is impure, since @a@ may expand
to an impure term such as @error@. -}
inlineImpure4 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
inlineImpure4 = mkInlinePurityTest $ do
  a <- freshName "a"
  let term =
        Force ()
          . Force ()
          . Force ()
          . Delay ()
          . Delay ()
          . Var ()
          $ a
  pure ([a], term)

{-| @(\a -> f (a 0 1) (a 2)) (\x y -> g x y)@

The first occurrence of `a` should be inlined because doing so does not increase
the size or the cost.

The second occurrence of `a` should be unconditionally inlined in the second simplifier
iteration, but in this test we are only running one iteration. -}
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
      termWithBoundTopLevel = LamAbs () f $ LamAbs () g $ Apply () fun arg
  pure termWithBoundTopLevel

multiApp :: Term Name PLC.DefaultUni PLC.DefaultFun ()
multiApp = runQuote $ do
  a <- freshName "a"
  b <- freshName "b"
  c <- freshName "c"
  let lam = LamAbs () a $ LamAbs () b $ LamAbs () c $ mkIterAppNoAnn (Var () c) [Var () a, Var () b]
      app =
        mkIterAppNoAnn
          lam
          [ mkConstant @Integer () 1
          , mkConstant @Integer () 2
          , mkConstant @Integer () 3
          ]
  pure app

forceDelayNoApps :: Term Name PLC.DefaultUni PLC.DefaultFun ()
forceDelayNoApps = runQuote $ do
  let one = mkConstant @Integer () 1
      term = Force () $ Delay () $ Force () $ Delay () $ Force () $ Delay () one
  pure term

forceDelayNoAppsLayered :: Term Name PLC.DefaultUni PLC.DefaultFun ()
forceDelayNoAppsLayered = runQuote $ do
  let one = mkConstant @Integer () 1
      term = Force () $ Force () $ Force () $ Delay () $ Delay () $ Delay () one
  pure term

{-| The UPLC term in this test should come from the following TPLC term after erasing its types:

> (/\(p :: *) -> \(x : p) -> /\(q :: *) -> \(y : q) -> /\(r :: *) -> \(z : r) -> z)
>   Int 1 Int 2 Int 3

This case is simple in the sense that each type abstraction
is followed by a single term abstraction. -}
forceDelaySimple :: Term Name PLC.DefaultUni PLC.DefaultFun ()
forceDelaySimple = runQuote $ do
  x <- freshName "x"
  y <- freshName "y"
  z <- freshName "z"
  let one = mkConstant @Integer () 1
      two = mkConstant @Integer () 2
      three = mkConstant @Integer () 3
      t = Delay () (LamAbs () x (Delay () (LamAbs () y (Delay () (LamAbs () z (Var () z))))))
      app = Apply () (Force () (Apply () (Force () (Apply () (Force () t) one)) two)) three
  pure app

{-| A test for the case when there are multiple applications between the 'Force' at the top
and the 'Delay' at the top of the term inside the abstractions/applications. -}
forceDelayMultiApply :: Term Name PLC.DefaultUni PLC.DefaultFun ()
forceDelayMultiApply = runQuote $ do
  x1 <- freshName "x1"
  x2 <- freshName "x2"
  x3 <- freshName "x3"
  f <- freshName "f"
  funcVar <- freshName "funcVar"
  let one = mkConstant @Integer () 1
      two = mkConstant @Integer () 2
      three = mkConstant @Integer () 3
      term =
        LamAbs () funcVar $
          Force () $
            mkIterAppNoAnn
              ( LamAbs () x1 $
                  LamAbs () x2 $
                    LamAbs () x3 $
                      LamAbs () f $
                        Delay () $
                          mkIterAppNoAnn (Var () f) [Var () x1, Var () x2, Var () x3]
              )
              [one, two, three, Var () funcVar]
  pure term

{-| A test for the case when there are multiple type abstractions over a single term
abstraction/application. -}
forceDelayMultiForce :: Term Name PLC.DefaultUni PLC.DefaultFun ()
forceDelayMultiForce = runQuote $ do
  x <- freshName "x"
  let one = mkConstant @Integer () 1
      term =
        Force () $
          Force () $
            Force () $
              Apply
                ()
                ( LamAbs () x $
                    Delay () $
                      Delay () $
                        Delay () $
                          Var () x
                )
                one
  pure term

{-| The UPLC term in this test should come from the following TPLC term after erasing its types:

> (/\(p1 :: *) (p2 :: *) -> \(x : p2) ->
>   /\(q1 :: *) (q2 :: *) (q3 :: *) -> \(y1 : q1) (y2 : q2) (y3 : String) ->
>     /\(r :: *) -> \(z1 : r) -> \(z2 : r) ->
>       /\(t :: *) -> \(f : p1 -> q1 -> q2 -> String -> r -> r -> String) ->
>         f x y1 y2 y3 z1 z2
> ) Int Int 1 Int String Int 2 "foo" "bar" Int 3 3 ByteString
> (funcVar : Int -> Int -> String -> String -> Int -> String)

Note this term has multiple interleaved type and term instantiations/applications. -}
forceDelayComplex :: Term Name PLC.DefaultUni PLC.DefaultFun ()
forceDelayComplex = runQuote $ do
  x <- freshName "x"
  y1 <- freshName "y1"
  y2 <- freshName "y2"
  y3 <- freshName "y3"
  z1 <- freshName "z1"
  z2 <- freshName "z2"
  f <- freshName "f"
  funcVar <- freshName "funcVar"
  let one = mkConstant @Integer () 1
      two = mkConstant @Integer () 2
      three = mkConstant @Integer () 3
      foo = mkConstant @Text () "foo"
      bar = mkConstant @Text () "bar"
      term =
        Delay () $
          Delay () $
            LamAbs () x $
              Delay () $
                Delay () $
                  Delay () $
                    LamAbs () y1 $
                      LamAbs () y2 $
                        LamAbs () y3 $
                          Delay () $
                            LamAbs () z1 $
                              LamAbs () z2 $
                                Delay () $
                                  LamAbs () f $
                                    mkIterAppNoAnn
                                      (Var () f)
                                      [ Var () x
                                      , Var () y1
                                      , Var () y2
                                      , Var () y3
                                      , Var () z1
                                      , Var () z2
                                      ]
      app =
        LamAbs () funcVar $
          Apply
            ()
            ( Force () $
                mkIterAppNoAnn
                  ( Force () $
                      mkIterAppNoAnn
                        ( Force () $
                            Force () $
                              Force () $
                                Apply
                                  ()
                                  (Force () $ Force () term)
                                  one
                        )
                        [two, foo, bar]
                  )
                  [three, three]
            )
            (Var () funcVar)
  pure app

forceCaseDelayNoApps1 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
forceCaseDelayNoApps1 = runQuote $ do
  scrut <- freshName "scrut"
  let one = mkConstant @Integer () 1
      term =
        LamAbs () scrut $
          Force () $
            Case () (Var () scrut) (V.fromList [Delay () one])
  pure term

forceCaseDelayWithApps1 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
forceCaseDelayWithApps1 = runQuote $ do
  scrut <- freshName "scrut"
  x <- freshName "x"
  let one = mkConstant @Integer () 1
      term =
        LamAbs () scrut $
          Force () $
            Case
              ()
              (Var () scrut)
              (V.fromList [LamAbs () x $ Delay () one])
  pure term

forceCaseDelayNoApps2 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
forceCaseDelayNoApps2 = runQuote $ do
  scrut <- freshName "scrut"
  let one = mkConstant @Integer () 1
      two = mkConstant @Integer () 2
      term =
        LamAbs () scrut $
          Force () $
            Case
              ()
              (Var () scrut)
              (V.fromList [Delay () one, Delay () two])
  pure term

forceCaseDelayWithApps2 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
forceCaseDelayWithApps2 = runQuote $ do
  scrut <- freshName "scrut"
  x <- freshName "x"
  let one = mkConstant @Integer () 1
      two = mkConstant @Integer () 2
      term =
        LamAbs () scrut $
          Force () $
            Case
              ()
              (Var () scrut)
              (V.fromList [LamAbs () x $ Delay () one, Delay () two])
  pure term

forceCaseDelayNoApps2Fail :: Term Name PLC.DefaultUni PLC.DefaultFun ()
forceCaseDelayNoApps2Fail = runQuote $ do
  scrut <- freshName "scrut"
  let one = mkConstant @Integer () 1
      two = mkConstant @Integer () 2
      term =
        LamAbs () scrut $
          Force () $
            Case
              ()
              (Var () scrut)
              (V.fromList [Delay () one, two])
  pure term

forceCaseDelayWithApps2Fail :: Term Name PLC.DefaultUni PLC.DefaultFun ()
forceCaseDelayWithApps2Fail = runQuote $ do
  scrut <- freshName "scrut"
  x <- freshName "x"
  y <- freshName "y"
  let one = mkConstant @Integer () 1
      two = mkConstant @Integer () 2
      term =
        LamAbs () scrut $
          Force () $
            Case
              ()
              (Var () scrut)
              ( V.fromList
                  [ LamAbs () x $ LamAbs () y $ Delay () one
                  , LamAbs () x two
                  ]
              )
  pure term

-- | This is the first example in Note [CSE].
cse1 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
cse1 = runQuote $ do
  x <- freshName "x"
  y <- freshName "y"
  let plus a b = mkIterApp (Builtin () PLC.AddInteger) [((), a), ((), b)]
      body = plus onePlusTwoPlusX caseExpr
      con = mkConstant @Integer ()
      twoPlusX = plus (con 2) (Var () x)
      onePlusTwoPlusX = plus (con 1) twoPlusX
      threePlusX = plus (con 3) (Var () x)
      fourPlusX = plus (con 4) (Var () x)
      branch1 = plus onePlusTwoPlusX threePlusX
      branch2 = plus twoPlusX threePlusX
      branch3 = fourPlusX
      caseExpr = Case () (Var () y) (V.fromList [branch1, branch2, branch3])
  pure $ LamAbs () x (LamAbs () y body)

-- | This is the second example in Note [CSE].
cse2 :: Term Name DefaultUni DefaultFun ()
cse2 = Force () (Force () body)
  where
    plus a b = mkIterApp (Builtin () PLC.AddInteger) [((), a), ((), b)]
    con = mkConstant @Integer ()
    body = mkIterApp (Builtin () PLC.IfThenElse) [((), cond), ((), true), ((), false)]
    cond = Apply () (Apply () (Builtin () PLC.LessThanInteger) (con 0)) (con 0)
    true = Delay () (plus (plus (con 1) (con 2)) (plus (con 1) (con 2)))
    false = Delay () (plus (con 1) (con 2))

-- | This is the third example in Note [CSE].
cse3 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
cse3 = runQuote $ do
  x <- freshName "x"
  y <- freshName "y"
  z <- freshName "z"
  f <- freshName "f"
  let plus a b = mkIterApp (Builtin () PLC.AddInteger) [((), a), ((), b)]
      con = mkConstant @Integer ()
      arg1 =
        mkIterApp
          (LamAbs () y (plus (con 1) (plus (Var () y) (Var () y))))
          [((), plus (con 0) (Var () x))]
      arg2 =
        mkIterApp
          (LamAbs () z (plus (con 2) (plus (Var () z) (Var () z))))
          [((), plus (con 0) (Var () x))]
  pure $ LamAbs () f $ LamAbs () x (mkIterApp (Var () f) [((), arg1), ((), arg2)])

--  ((1+2) + (3+4) + ...)
--  +
--  ((1+2) + (3+4) + ...)
cseExpensive :: Term Name DefaultUni DefaultFun ()
cseExpensive = plus arg arg'
  where
    plus a b = mkIterApp (Builtin () PLC.AddInteger) [((), a), ((), b)]
    con = mkConstant @Integer ()
    mkArg = foldl1 plus . fmap (\i -> plus (con (2 * i)) (con (2 * i + 1)))
    arg = mkArg [0 .. 200]
    arg' = mkArg [0 .. 200]

-- tree where nodes are + and leaves are constants
csePlusTree :: Term Name DefaultUni DefaultFun ()
csePlusTree = go 5
  where
    go :: Int -> Term Name DefaultUni DefaultFun ()
    go 0 = con 1
    go n = plus (go (n - 1)) (go (n - 1))

    plus a b = mkIterApp (Builtin () PLC.AddInteger) [((), a), ((), b)]
    con = mkConstant @Integer ()

-- (1 + (1 + ... + 0))
-- optimised to
-- let f = (1 +) in f (f (... 0))
cseRepeatPlus :: Term Name DefaultUni DefaultFun ()
cseRepeatPlus = go 5
  where
    go :: Int -> Term Name DefaultUni DefaultFun ()
    go 0 = con 0
    go n = plus (con 1) (go (n - 1))

    plus a b = mkIterApp (Builtin () PLC.AddInteger) [((), a), ((), b)]
    con = mkConstant @Integer ()

testSimplifyInputs :: [(String, Term Name PLC.DefaultUni PLC.DefaultFun ())]
testSimplifyInputs =
  [ ("basic", basic)
  , ("nested", nested)
  , ("extraDelays", extraDelays)
  , ("floatDelay1", floatDelay1)
  , ("floatDelay2", floatDelay2)
  , ("floatDelay3", floatDelay3)
  , ("interveningLambda", interveningLambda)
  , ("basicInline", basicInline)
  , ("callsiteInline", callsiteInline)
  , ("inlinePure1", inlinePure1)
  , ("inlinePure2", inlinePure2)
  , ("inlinePure3", inlinePure3)
  , ("inlinePure4", inlinePure4)
  , ("inlineImpure1", inlineImpure1)
  , ("inlineImpure2", inlineImpure2)
  , ("inlineImpure3", inlineImpure3)
  , ("inlineImpure4", inlineImpure4)
  , ("multiApp", multiApp)
  , ("forceDelayNoApps", forceDelayNoApps)
  , ("forceDelayNoAppsLayered", forceDelayNoAppsLayered)
  , ("forceDelaySimple", forceDelaySimple)
  , ("forceDelayMultiApply", forceDelayMultiApply)
  , ("forceDelayMultiForce", forceDelayMultiForce)
  , ("forceDelayComplex", forceDelayComplex)
  , ("forceCaseDelayNoApps1", forceCaseDelayNoApps1)
  , ("forceCaseDelayWithApps1", forceCaseDelayWithApps1)
  , ("forceCaseDelayNoApps2", forceCaseDelayNoApps2)
  , ("forceCaseDelayWithApps2", forceCaseDelayWithApps2)
  , ("forceCaseDelayNoApps2Fail", forceCaseDelayNoApps2Fail)
  , ("forceCaseDelayWithApps2Fail", forceCaseDelayWithApps2Fail)
  ]

testCseInputs :: [(String, Term Name PLC.DefaultUni PLC.DefaultFun ())]
testCseInputs =
  [ ("cse1", cse1)
  , ("cse2", cse2)
  , ("cse3", cse3)
  , ("cseExpensive", cseExpensive)
  ]

testCseInputsWorkFree :: [(String, Term Name PLC.DefaultUni PLC.DefaultFun ())]
testCseInputsWorkFree =
  [ ("cse1WorkFree", cse1)
  , ("csePlusTree", csePlusTree)
  , ("cseRepeatPlus", cseRepeatPlus)
  ]

test_simplify :: TestTree
test_simplify =
  testGroup
    "simplify"
    $ fmap (uncurry goldenVsSimplified) testSimplifyInputs
      <> fmap (uncurry (goldenVsCse ExcludeWorkFree)) testCseInputs
      <> fmap (uncurry (goldenVsCse AllSubterms)) testCseInputsWorkFree
