module Transform.Simplify.Spec where

import PlutusCore qualified as PLC
import PlutusCore.MkPlc (mkIterApp, mkIterAppNoAnn)
import Test.Tasty (TestTree, testGroup)
import Transform.Lib
  ( T
  , app
  , builtin
  , case_
  , con
  , constr
  , delay
  , err
  , force
  , ite
  , lam
  , name
  , sopFalse
  , sopTrue
  , text
  , var
  )
import Transform.Simplify.Lib (goldenVsCse, goldenVsOptimized)
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
basic = force $ delay $ con 1

nested :: Term Name PLC.DefaultUni PLC.DefaultFun ()
nested = force $ force $ delay $ delay $ con 1

extraDelays :: Term Name PLC.DefaultUni PLC.DefaultFun ()
extraDelays = force $ delay $ delay $ con 1

interveningLambda :: Term Name PLC.DefaultUni PLC.DefaultFun ()
interveningLambda = force (lam "a" (delay (var "a" `app` var "a")) `app` con 1)

caseOfCase1 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
caseOfCase1 = case_ (ite (var "b") sopTrue sopFalse) [con 1, con 2]

{-| This should not simplify, because one of the branches of `ifThenElse` is not a `Constr`.
Unless both branches are known constructors, the case-of-case transformation
may increase the program size. -}
caseOfCase2 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
caseOfCase2 = case_ (ite (var "b") (var "t") sopFalse) [con 1, con 2]

{-| Similar to `caseOfCase1`, but the type of the @true@ and @false@ branches is
@[Integer]@ rather than Bool (note that @Constr 0@ has two parameters, @x@ and @xs@). -}
caseOfCase3 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
caseOfCase3 = case_ (ite (var "b") trueBranch sopFalse) [var "f", con 2]
  where
    trueBranch = constr 0 [var "x", var "xs"]

-- | The `Delay` should be floated into the lambda.
floatDelay1 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
floatDelay1 = lam "a" (force (var "a") `plus` force (var "a")) `app` delay (con 1)

{-| The `Delay` should not be floated into the lambda, because the argument (1 + 2)
is not work-free. -}
floatDelay2 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
floatDelay2 =
  lam "a" (force (var "a") `plus` force (var "a"))
    `app` delay (con 1 `plus` con 2)

{-| The `Delay` should not be floated into the lambda in the first simplifier iteration,
because one of the occurrences of `a` is not under `Force`. It should be floated into
the lambda in the second simplifier iteration, after `b` is inlined. -}
floatDelay3 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
floatDelay3 =
  lam "a" (force (var "a") `plus` force (lam "b" (var "b") `app` var "a"))
    `app` delay (con 1)

{-| The 'Delay' should not be floated into the lambda because the argument to the 'Delay' is
not pure. -}
floatDelay4 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
floatDelay4 = lam "a" body `app` delay (constr 0 [err])
  where
    body = case_ (constr 0 []) [con 1, force (var "a")]

basicInline :: Term Name PLC.DefaultUni PLC.DefaultFun ()
basicInline = lam "a" (var "a") `app` con 1

{-| A helper function to create a term which tests whether the inliner
behaves as expected for a given pure or impure term. It receives a term
together with a list of its free variables. The free variables are bound
at the top level of the final term in order to ensure that the produced
final term is well-scoped. -}
mkInlinePurityTest
  :: ([Name], Term Name PLC.DefaultUni PLC.DefaultFun ())
  -> Term Name PLC.DefaultUni PLC.DefaultFun ()
mkInlinePurityTest (freeVars, term) =
  -- In `[(\a . \b . a) term]`, `term` will be inlined if and only if it is pure.
  mkIterLamAbs (UVarDecl () <$> freeVars) $
    lam "a" (lam "b" (var "a")) `app` term

-- | A single @Var@ is pure.
inlinePure1 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
inlinePure1 = mkInlinePurityTest ([name "a"], var "a")

{-| @force (delay a)@ is pure.

Note that this relies on @forceDelayCancel@ to cancel the @force@ and the @delay@,
otherwise the inliner would treat the term as impure. -}
inlinePure2 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
inlinePure2 = mkInlinePurityTest ([name "a"], force $ delay (var "a"))

{-| @[(\x -> \y -> [x x]) (con integer 1)]@ is pure.

Note that the @(con integer 1)@ won't get inlined: it isn't pre-inlined because
@x@ occurs twice, and it isn't post-inlined because @costIsAcceptable Constant{} = False@.
However, the entire term will be inlined since it is pure. -}
inlinePure3 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
inlinePure3 =
  mkInlinePurityTest
    ([], app (lam "x" $ lam "y" $ var "x" `app` var "x") (con 1))

{-| @force ([(\x -> delay (\y -> [x x])) (delay ([error (con integer 1)]))])@ is pure,
but it is very tricky to see so. It requires us to match up a force and a
delay through several steps of intervening computation. -}
inlinePure4 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
inlinePure4 =
  mkInlinePurityTest
    ( []
    , force $
        lam "x" (delay (lam "y" (var "x" `app` var "x")))
          `app` delay (err `app` con 1)
    )

-- | @error@ is impure.
inlineImpure1 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
inlineImpure1 = mkInlinePurityTest ([], err)

-- | @force (delay error)@ is impure.
inlineImpure2 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
inlineImpure2 = mkInlinePurityTest ([], force (delay err))

{-| @force (force (force (delay (delay (delay (error))))))@ is impure, since it
is the same as @error@. -}
inlineImpure3 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
inlineImpure3 =
  mkInlinePurityTest ([], force . force . force . delay . delay $ delay err)

{-| @force (force (force (delay (delay a))))@ is impure, since @a@ may expand
to an impure term such as @error@. -}
inlineImpure4 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
inlineImpure4 =
  mkInlinePurityTest
    ( [name "a"]
    , force . force . force . delay . delay $ var "a"
    )

{-| @(\a -> f (a 0 1) (a 2)) (\x y -> g x y)@

The first occurrence of `a` should be inlined because doing so does not increase
the size or the cost.

The second occurrence of `a` should be unconditionally inlined in the second simplifier
iteration, but in this test we are only running one iteration. -}
callsiteInline :: Term Name PLC.DefaultUni PLC.DefaultFun ()
callsiteInline = lam "f" $ lam "g" $ app fun arg
  where
    fun =
      lam "a" $
        mkIterAppNoAnn
          (var "f")
          [ mkIterAppNoAnn (var "a") [con 0, con 1]
          , mkIterAppNoAnn (var "a") [con 2]
          ]
    arg =
      lam "x" . lam "y" $
        mkIterAppNoAnn (var "g") [var "y", var "x"]

multiApp :: Term Name PLC.DefaultUni PLC.DefaultFun ()
multiApp = mkIterAppNoAnn applyLam [con 1, con 2, con 3]
  where
    applyLam =
      lam "a" $
        lam "b" $
          lam "c" $
            mkIterAppNoAnn (var "c") [var "a", var "b"]

forceDelayNoApps :: Term Name PLC.DefaultUni PLC.DefaultFun ()
forceDelayNoApps = force $ delay $ force $ delay $ force $ delay $ con 1

forceDelayNoAppsLayered :: Term Name PLC.DefaultUni PLC.DefaultFun ()
forceDelayNoAppsLayered = force $ force $ force $ delay $ delay $ delay $ con 1

{-| The UPLC term in this test should come from the following TPLC term after erasing its types:

> (/\(p :: *) -> \(x : p) -> /\(q :: *) -> \(y : q) -> /\(r :: *) -> \(z : r) -> z)
>   Int 1 Int 2 Int 3

This case is simple in the sense that each type abstraction
is followed by a single term abstraction. -}
forceDelaySimple :: Term Name PLC.DefaultUni PLC.DefaultFun ()
forceDelaySimple = force (force (force t `app` con 1) `app` con 2) `app` con 3
  where
    t = delay (lam "x" (delay (lam "y" (delay (lam "z" (var "z"))))))

{-| A test for the case when there are multiple applications between the 'Force' at the top
and the 'Delay' at the top of the term inside the abstractions/applications. -}
forceDelayMultiApply :: Term Name PLC.DefaultUni PLC.DefaultFun ()
forceDelayMultiApply =
  lam "funcVar" $
    force $
      mkIterAppNoAnn
        ( lam "x1" $
            lam "x2" $
              lam "x3" $
                lam "f" $
                  delay $
                    mkIterAppNoAnn (var "f") [var "x1", var "x2", var "x3"]
        )
        [con 1, con 2, con 3, var "funcVar"]

{-| A test for the case when there are multiple type abstractions over a single term
abstraction/application. -}
forceDelayMultiForce :: Term Name PLC.DefaultUni PLC.DefaultFun ()
forceDelayMultiForce =
  force $ force $ force $ app (lam "x" $ delay $ delay $ delay (var "x")) (con 1)

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
forceDelayComplex = whole
  where
    term =
      delay
        . delay
        . lam "x"
        . delay
        . delay
        . delay
        . lam "y1"
        . lam "y2"
        . lam "y3"
        . delay
        . lam "z1"
        . lam "z2"
        . delay
        . lam "f"
        $ mkIterAppNoAnn
          (var "f")
          [ var "x"
          , var "y1"
          , var "y2"
          , var "y3"
          , var "z1"
          , var "z2"
          ]
    whole =
      lam "funcVar" $
        app
          ( force $
              mkIterAppNoAnn
                ( force $
                    mkIterAppNoAnn
                      (force (force (force (force (force term) `app` con 1))))
                      [ con 2
                      , text "foo"
                      , text "bar"
                      ]
                )
                [ con 3
                , con 3
                ]
          )
          (var "funcVar")

forceCaseDelayNoApps1 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
forceCaseDelayNoApps1 =
  lam "scrut" $ force $ case_ (var "scrut") [delay (con 1)]

forceCaseDelayWithApps1 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
forceCaseDelayWithApps1 =
  lam "scrut" $ force $ case_ (var "scrut") [lam "x" $ delay (con 1)]

forceCaseDelayNoApps2 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
forceCaseDelayNoApps2 =
  lam "scrut" $ force $ case_ (var "scrut") [delay (con 1), delay (con 2)]

forceCaseDelayWithApps2 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
forceCaseDelayWithApps2 =
  lam "scrut" $
    force $
      case_ (var "scrut") [lam "x" $ delay (con 1), delay (con 2)]

forceCaseDelayNoApps2Fail :: Term Name PLC.DefaultUni PLC.DefaultFun ()
forceCaseDelayNoApps2Fail =
  lam "scrut" $ force $ case_ (var "scrut") [delay (con 1), con 2]

forceCaseDelayWithApps2Fail :: Term Name PLC.DefaultUni PLC.DefaultFun ()
forceCaseDelayWithApps2Fail =
  lam "scrut" $
    force $
      case_
        (var "scrut")
        [ lam "x" (lam "y" (delay (con 1)))
        , lam "x" (con 2)
        ]

-- case ((\x -> constr 0 []) 1) [42]
letFloatOutCase1 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
letFloatOutCase1 = case_ (lam "x" sopTrue `app` con 1) [con 42]

-- \a -> case ((\x -> constr 0 [x, x]) a) addInteger
letFloatOutCase2 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
letFloatOutCase2 = lam "a" $ case_ binding [builtin PLC.AddInteger]
  where
    body = constr 0 [var "x", var "x"]
    binding = lam "x" body `app` var "a"

-- \a -> force ((\x -> delay x) a)
letFloatOutForce :: Term Name PLC.DefaultUni PLC.DefaultFun ()
letFloatOutForce = lam "a" (force binding)
  where
    delayLam = lam "x" (delay (var "x"))
    binding = delayLam `app` var "a"

-- | This is the first example in Note [CSE].
cse1 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
cse1 = lam "x" (lam "y" (plus onePlusTwoPlusX caseExpr))
  where
    twoPlusX = plus (con 2) (var "x")
    onePlusTwoPlusX = plus (con 1) twoPlusX
    threePlusX = plus (con 3) (var "x")
    fourPlusX = plus (con 4) (var "x")
    branch1 = plus onePlusTwoPlusX threePlusX
    branch2 = plus twoPlusX threePlusX
    branch3 = fourPlusX
    caseExpr = case_ (var "y") [branch1, branch2, branch3]

-- | This is the second example in Note [CSE].
cse2 :: Term Name DefaultUni DefaultFun ()
cse2 = force (force body)
  where
    body = mkIterApp (builtin PLC.IfThenElse) [((), cond), ((), trueBranch), ((), falseBranch)]
    cond = builtin PLC.LessThanInteger `app` con 0 `app` con 0
    trueBranch = delay (plus (plus (con 1) (con 2)) (plus (con 1) (con 2)))
    falseBranch = delay (plus (con 1) (con 2))

-- | This is the third example in Note [CSE].
cse3 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
cse3 = lam "f" $ lam "x" $ var "f" `app` arg1 `app` arg2
  where
    arg1 =
      lam "y" (plus (con 1) (plus (var "y") (var "y")))
        `app` plus (con 0) (var "x")
    arg2 =
      lam "z" (plus (con 2) (plus (var "z") (var "z")))
        `app` plus (con 0) (var "x")

--  ((1+2) + (3+4) + ...)
--  +
--  ((1+2) + (3+4) + ...)
cseExpensive :: Term Name DefaultUni DefaultFun ()
cseExpensive = mkArg [0 .. 200] `plus` mkArg [0 .. 200]
  where
    mkArg = foldl1 plus . map (\i -> plus (con (2 * i)) (con (2 * i + 1)))

-- tree where nodes are + and leaves are constants
csePlusTree :: Term Name DefaultUni DefaultFun ()
csePlusTree = go 5
  where
    go :: Int -> T
    go 0 = con 1
    go n = plus (go (n - 1)) (go (n - 1))

-- (1 + (1 + ... + 0))
-- optimised to
-- let f = (1 +) in f (f (... 0))
cseRepeatPlus :: Term Name DefaultUni DefaultFun ()
cseRepeatPlus = go 5
  where
    go :: Int -> T
    go 0 = con 0
    go n = plus (con 1) (go (n - 1))

testSimplifyInputs :: [(String, Term Name PLC.DefaultUni PLC.DefaultFun ())]
testSimplifyInputs =
  [ ("basic", basic)
  , ("nested", nested)
  , ("extraDelays", extraDelays)
  , ("floatDelay1", floatDelay1)
  , ("floatDelay2", floatDelay2)
  , ("floatDelay3", floatDelay3)
  , ("floatDelay4", floatDelay4)
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
  , ("letFloatOutCase1", letFloatOutCase1)
  , ("letFloatOutCase2", letFloatOutCase2)
  , ("letFloatOutForce", letFloatOutForce)
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
    $ fmap (uncurry goldenVsOptimized) testSimplifyInputs
      <> fmap (uncurry (goldenVsCse ExcludeWorkFree)) testCseInputs
      <> fmap (uncurry (goldenVsCse AllSubterms)) testCseInputsWorkFree

--------------------------------------------------------------------------------
-- Local helpers ---------------------------------------------------------------

plus :: T -> T -> T
plus i j = builtin PLC.AddInteger `app` i `app` j
