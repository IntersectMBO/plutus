{-# LANGUAGE BlockArguments    #-}
{-# LANGUAGE OverloadedStrings #-}

module Transform.Simplify where

import PlutusCore qualified as PLC
import Test.Tasty (TestTree, testGroup)
import Transform.Simplify.Lib (goldenVsCse, goldenVsSimplified)
import UntypedPlutusCore (DefaultFun, DefaultUni, Name, Term (..))
import UntypedPlutusCore.Test.Term.Construction (addInteger, app, case_, ctor, ctorFalse, ctorTrue,
                                                 delay, err, force, ifThenElse, int, lam,
                                                 lessThanInteger, name, string, uniqueNames2,
                                                 uniqueNames3, uniqueNames4, uniqueNames5,
                                                 uniqueNames8, var)

basic :: Term Name PLC.DefaultUni PLC.DefaultFun ()
basic = force (delay (int 1))

nested :: Term Name PLC.DefaultUni PLC.DefaultFun ()
nested = force (force (delay (delay (int 1))))

extraDelays :: Term Name PLC.DefaultUni PLC.DefaultFun ()
extraDelays = force (delay (delay (int 1)))

interveningLambda :: Term Name PLC.DefaultUni PLC.DefaultFun ()
interveningLambda =
  force (app (lam n (delay (var n `app` var n))) (int 1))
 where
  n = name "n" 0

caseOfCase1 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
caseOfCase1 =
  case_
    (ifThenElse (var (name "b" 0)) ctorTrue ctorFalse)
    [int 1, int 2]

{-| This should not simplify, because one of the branches of `ifThenElse` is not a `Constr`.
Unless both branches are known constructors, the case-of-case transformation
may increase the program size.
-}
caseOfCase2 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
caseOfCase2 = case_ (ifThenElse (var b) (var t) (ctor 1 [])) [int 1, int 2]
 where
  (b, t) = uniqueNames2 "b" "t"

{-| Similar to `caseOfCase1`, but the type of the @true@ and @false@ branches is
@[Integer]@ rather than Bool (note that @Constr 0@ has two parameters, @x@ and @xs@).
-}
caseOfCase3 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
caseOfCase3 =
  case_
    ( ifThenElse
        (var b)
        (ctor 0 [var x, var xs])
        ctorFalse
    )
    [ var f
    , int 2
    ]
 where
  (b, x, xs, f) = uniqueNames4 "b" "x" "xs" "f"

-- | The `Delay` should be floated into the lambda.
floatDelay1 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
floatDelay1 =
  lam a (force (var a) `addInteger` force (var a))
    `app` delay (int 1)
 where
  a = name "a" 0

{-| The `Delay` should not be floated into the lambda, because the argument (1 + 2)
is not work-free.
-}
floatDelay2 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
floatDelay2 =
  lam a (force (var a) `addInteger` force (var a))
    `app` delay (int 1 `addInteger` int 2)
 where
  a = name "a" 0

{-| The `Delay` should not be floated into the lambda in the first simplifier iteration,
because one of the occurrences of `a` is not under `Force`. It should be floated into
the lambda in the second simplifier iteration, after `b` is inlined.
-}
floatDelay3 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
floatDelay3 =
  lam a (force (var a) `addInteger` force (lam b (var b) `app` var a))
    `app` delay (int 1)
 where
  (a, b) = uniqueNames2 "a" "b"

basicInline :: Term Name PLC.DefaultUni PLC.DefaultFun ()
basicInline = lam n (var n) `app` int 1
 where
  n = name "n" 0

mkInlinePurityTest
  :: Term Name PLC.DefaultUni PLC.DefaultFun ()
  -> Term Name PLC.DefaultUni PLC.DefaultFun ()
mkInlinePurityTest termToInline =
  -- In `[(\a . \b . a) termToInline]`, `termToInline` will be inlined
  -- if and only if it is pure.
  lam a (lam b (var a)) `app` termToInline
 where
  (a, b) = uniqueNames2 "a" "b"

-- | A single @Var@ is pure.
inlinePure1 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
inlinePure1 = mkInlinePurityTest $ var (name "a" 0)

{-| @force (delay a)@ is pure.

Note that this relies on @forceDelayCancel@ to cancel the @force@ and the @delay@,
otherwise the inliner would treat the term as impure.
-}
inlinePure2 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
inlinePure2 = mkInlinePurityTest $ force . delay $ var $ name "a" 0

{-| @[(\x -> \y -> [x x]) (int integer 1)]@ is pure.

Note that the @(int integer 1)@ won't get inlined: it isn't pre-inlined because
@x@ occurs twice, and it isn't post-inlined because @costIsAcceptable Constant{} = False@.
However, the entire term will be inlined since it is pure.
-}
inlinePure3 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
inlinePure3 = mkInlinePurityTest $ lam x (lam y (var x `app` var x)) `app` int 1
 where
  (x, y) = uniqueNames2 "x" "y"

{-| @force ([(\x -> delay (\y -> [x x])) (delay ([error (int integer 1)]))])@ is pure,
but it is very tricky to see so. It requires us to match up a force and a
delay through several steps of intervening computation.
-}
inlinePure4 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
inlinePure4 =
  mkInlinePurityTest $
    force $
      lam x (delay (lam y (var x `app` var x)))
        `app` delay (app err (int 1))
 where
  (x, y) = uniqueNames2 "x" "y"

-- | @error@ is impure.
inlineImpure1 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
inlineImpure1 = mkInlinePurityTest err

-- | @force (delay error)@ is impure.
inlineImpure2 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
inlineImpure2 = mkInlinePurityTest $ force $ delay err

{-| @force (force (force (delay (delay (delay (error))))))@ is impure, since it
is the same as @error@.
-}
inlineImpure3 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
inlineImpure3 =
  mkInlinePurityTest $
    force . force . force . delay . delay $
      delay err

{-| @force (force (force (delay (delay a))))@ is impure, since @a@ may expand
to an impure term such as @error@.
-}
inlineImpure4 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
inlineImpure4 =
  mkInlinePurityTest $ force . force . force . delay . delay . var $ name "a" 0

{-| @(\a -> f (a 0 1) (a 2)) (\x y -> g x y)@

The first occurrence of `a` should be inlined because doing so does not increase
the size or the cost.

The second occurrence of `a` should be unconditionally inlined in the second simplifier
iteration, but in this test we are only running one iteration.
-}
callsiteInline :: Term Name PLC.DefaultUni PLC.DefaultFun ()
callsiteInline =
  lam
    a
    ( var f
        `app` (var a `app` int 0 `app` int 1)
        `app` (var a `app` int 2)
    )
    `app` lam x (lam y (var g `app` var y `app` var x))
 where
  (a, f, x, y, g) = uniqueNames5 "a" "f" "x" "y" "g"

multiApp :: Term Name PLC.DefaultUni PLC.DefaultFun ()
multiApp =
  ( lam a $
      lam b $
        lam c $
          var c `app` var a `app` var b
  )
    `app` int 1
    `app` int 2
    `app` int 3
 where
  (a, b, c) = uniqueNames3 "a" "b" "c"

forceDelayNoApps :: Term Name PLC.DefaultUni PLC.DefaultFun ()
forceDelayNoApps = force $ delay $ force $ delay $ force $ delay $ int 1

forceDelayNoAppsLayered :: Term Name PLC.DefaultUni PLC.DefaultFun ()
forceDelayNoAppsLayered = force $ force $ force $ delay $ delay $ delay $ int 1

{-| The UPLC term in this test should come from the following TPLC term after erasing its types:

> (/\(p :: *) -> \(x : p) -> /\(q :: *) -> \(y : q) -> /\(r :: *) -> \(z : r) -> z)
>   Int 1 Int 2 Int 3

This case is simple in the sense that each type abstraction
is followed by a single term abstraction.
-}
forceDelaySimple :: Term Name PLC.DefaultUni PLC.DefaultFun ()
forceDelaySimple = force (force (force t `app` int 1) `app` int 2) `app` int 3
 where
  t = delay (lam x (delay (lam y (delay (lam z (var z))))))
  (x, y, z) = uniqueNames3 "x" "y" "z"

{-| A test for the case when there are multiple applications between the
'Force' at the top and the 'Delay' at the top of the term inside the
abstractions/applications.
-}
forceDelayMultiApply :: Term Name PLC.DefaultUni PLC.DefaultFun ()
forceDelayMultiApply =
  force
    ( ( lam x1 $
          lam x2 $
            lam x3 $
              lam f $
                delay $
                  var f `app` var x1 `app` var x2 `app` var x3
      )
        `app` int 1
        `app` int 2
        `app` int 3
        `app` var funcVar
    )
 where
  (x1, x2, x3, f, funcVar) = uniqueNames5 "x1" "x2" "x3" "f" "funcVar"

{-| A test for the case when there are multiple type abstractions over a
single term abstraction/application.
-}
forceDelayMultiForce :: Term Name PLC.DefaultUni PLC.DefaultFun ()
forceDelayMultiForce =
  force (force (force (lam x (delay (delay (delay (var x)))) `app` int 1)))
 where
  x = name "x" 0

{-| The UPLC term in this test should come from the following TPLC
 term after erasing its types:

> (/\(p1 :: *) (p2 :: *) -> \(x : p2) ->
>   /\(q1 :: *) (q2 :: *) (q3 :: *) -> \(y1 : q1) (y2 : q2) (y3 : String) ->
>     /\(r :: *) -> \(z1 : r) -> \(z2 : r) ->
>       /\(t :: *) -> \(f : p1 -> q1 -> q2 -> String -> r -> r -> String) ->
>         f x y1 y2 y3 z1 z2
> ) Int Int 1 Int String Int 2 "foo" "bar" Int 3 3 ByteString
> (funcVar : Int -> Int -> String -> String -> Int -> String)

Note this term has multiple interleaved type and term instantiations/applications.
-}
forceDelayComplex :: Term Name PLC.DefaultUni PLC.DefaultFun ()
forceDelayComplex =
  force
    ( force
        ( force (force (force (force (force term) `app` int 1)))
            `app` int 2
            `app` string "foo"
            `app` string "bar"
        )
        `app` int 3
        `app` int 3
    )
    `app` var funcVar
 where
  term =
    delay $
      delay $
        lam x $
          delay $
            delay $
              delay $
                lam y1 $
                  lam y2 $
                    lam y3 $
                      delay $
                        lam z1 $
                          lam z2 $
                            delay $
                              lam f $
                                var f
                                  `app` var x
                                  `app` var y1
                                  `app` var y2
                                  `app` var y3
                                  `app` var z1
                                  `app` var z2

  (x, y1, y2, y3, z1, z2, f, funcVar) =
    uniqueNames8 "x" "y1" "y2" "y3" "z1" "z2" "f" "funcVar"

-- | This is the first example in Note [CSE].
cse1 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
cse1 = lam x (lam y (addInteger onePlusTwoPlusX caseExpr))
 where
  twoPlusX = addInteger (int 2) (var x)
  threePlusX = addInteger (int 3) (var x)
  onePlusTwoPlusX = addInteger (int 1) twoPlusX
  caseExpr =
    case_
      (var y)
      [ addInteger onePlusTwoPlusX threePlusX
      , addInteger twoPlusX threePlusX
      , addInteger (int 4) (var x)
      ]
  (x, y) = uniqueNames2 "x" "y"

-- | This is the second example in Note [CSE].
cse2 :: Term Name DefaultUni DefaultFun ()
cse2 =
  force $
    ifThenElse
      (int 0 `lessThanInteger` int 0)
      (delay (addInteger (int 1 `addInteger` int 2) (int 1 `addInteger` int 2)))
      (delay (addInteger (int 1) (int 2)))

-- | This is the third example in Note [CSE].
cse3 :: Term Name PLC.DefaultUni PLC.DefaultFun ()
cse3 =
  lam x $
    var f
      `app` ( lam y (int 1 `addInteger` (var y `addInteger` var y))
                `app` addInteger (int 0) (var x)
            )
      `app` ( lam z (int 2 `addInteger` (var z `addInteger` var z))
                `app` addInteger (int 0) (var x)
            )
 where
  (x, y, z, f) = uniqueNames4 "x" "y" "z" "f"

--  ((1+2) + (3+4) + ...)
--  +
--  ((1+2) + (3+4) + ...)
cseExpensive :: Term Name DefaultUni DefaultFun ()
cseExpensive = addInteger (mkArg [0 .. 200]) (mkArg [0 .. 200])
 where
  mkArg =
    foldl1 addInteger . map \i ->
      int (2 * i) `addInteger` int (2 * i + 1)

test_simplify :: TestTree
test_simplify =
  testGroup
    "simplify"
    [ goldenVsSimplified "basic" basic
    , goldenVsSimplified "nested" nested
    , goldenVsSimplified "extraDelays" extraDelays
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
    , goldenVsSimplified "forceDelayNoApps" forceDelayNoApps
    , goldenVsSimplified "forceDelayNoAppsLayered" forceDelayNoAppsLayered
    , goldenVsSimplified "forceDelaySimple" forceDelaySimple
    , goldenVsSimplified "forceDelayMultiApply" forceDelayMultiApply
    , goldenVsSimplified "forceDelayMultiForce" forceDelayMultiForce
    , goldenVsSimplified "forceDelayComplex" forceDelayComplex
    , goldenVsCse "cse1" cse1
    , goldenVsCse "cse2" cse2
    , goldenVsCse "cse3" cse3
    , goldenVsCse "cseExpensive" cseExpensive
    ]
