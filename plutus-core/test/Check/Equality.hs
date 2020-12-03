{-# LANGUAGE OverloadedStrings #-}

module Check.Equality
    ( test_equality
    ) where

import           Language.PlutusCore
import           Language.PlutusCore.MkPlc
import           Language.PlutusCore.Pretty

import           Control.Monad
import           Data.Foldable
import           Data.List
import           Data.Traversable
import           Test.Tasty
import           Test.Tasty.HUnit

testAlphaEquality :: Bool
testAlphaEquality =
    let
        xName = Name "x" (Unique 0)
        yName = Name "y" (Unique 1)

        varX = Var () xName
        varY = Var () yName

        varType = TyVar () (TyName (Name "a" (Unique 2)))

        lamX = LamAbs () xName varType varX
        lamY = LamAbs () yName varType varY

        term0, term1 :: Term TyName Name DefaultUni DefaultFun ()

        -- [(lam x a x) x]
        term0 = Apply () lamX varX
        -- [(lam y a y) x]
        term1 = Apply () lamY varX

    in
        term0 == term1

testRebindShadowedVariable :: Bool
testRebindShadowedVariable =
    let
        xName = TyName (Name "x" (Unique 0))
        yName = TyName (Name "y" (Unique 1))
        zName = TyName (Name "z" (Unique 2))

        varX = TyVar () xName
        varY = TyVar () yName
        varZ = TyVar () zName

        typeKind = Type ()

        l1, r1, l2, r2 :: Type TyName DefaultUni ()

        -- (all x (type) (fun (all y (type) y) x))
        l1 = TyForall () xName typeKind (TyFun () (TyForall () yName typeKind varY) varX)
        -- (all x (type) (fun (all x (type) x) x))
        r1 = TyForall () xName typeKind (TyFun () (TyForall () xName typeKind varX) varX)

        -- (all x (type) (all x (type) (fun x x)))
        l2 = TyForall () xName typeKind (TyForall () xName typeKind (TyFun () varX varX))
        -- (all y (type) (all z (type) (fun y z)))
        r2 = TyForall () yName typeKind (TyForall () zName typeKind (TyFun () varY varZ))

    in
        l1 == r1 && l2 /= r2

testRebindCapturedVariable :: Bool
testRebindCapturedVariable =
    let
        wName = TyName (Name "w" (Unique 0))
        xName = TyName (Name "x" (Unique 1))
        yName = TyName (Name "y" (Unique 2))
        zName = TyName (Name "z" (Unique 3))

        varW = TyVar () wName
        varX = TyVar () xName
        varY = TyVar () yName
        varZ = TyVar () zName

        typeKind = Type ()

        typeL1, typeR1, typeL2, typeR2 :: Type TyName DefaultUni ()

        -- (all y (type) (all z (type) (fun y z)))
        typeL1 = TyForall () yName typeKind (TyForall () zName typeKind (TyFun () varY varZ))
        -- (all x (type) (all y (type) (fun x y)))
        typeR1 = TyForall () xName typeKind (TyForall () yName typeKind (TyFun () varX varY))

        -- (all z (type) (fun (all w (all x (type) (fun w x))))) z)
        typeL2
            = TyForall () zName typeKind
            $ TyFun ()
                (TyForall () wName typeKind $ TyForall () xName typeKind (TyFun () varW varX))
                varZ
        -- (all x (type) (fun (all x (all y (type) (fun x y))))) x)
        typeR2
            = TyForall () xName typeKind
            $ TyFun ()
                (TyForall () xName typeKind $ TyForall () yName typeKind (TyFun () varX varY))
                varX
    in [typeL1, typeL2] == [typeR1, typeR2]

allDistinct :: Eq a => [a] -> Bool
allDistinct []     = True
allDistinct (x:xs) = x `notElem` xs && allDistinct xs

splits :: [a] -> [([a], [a])]
splits xs = zip (inits xs) (tails xs)

-- This generates thousands of test cases.
tyEtaPairs :: [(Type TyName DefaultUni (), Type TyName DefaultUni (), Bool)]
tyEtaPairs = do
    let (x, y, f) = runQuote $ (,,) <$> freshTyName "x" <*> freshTyName "y" <*> freshTyName "f"
        -- @varRows 2 ~> [[],[x],[y],[x,x],[x,y],[y,x],[y,y]]@
        varRows n = [0..n] >>= \i -> replicateM i [x, y]
    -- The 'x' variable always goes first, because if we also allowed 'y' to go first,
    -- that would just duplicate all the tests as @\x y -> x@ and @\y x -> y@ are alpha-equal.
    binds1 <- map (x :) (varRows 2)
    args1  <- do
        -- Here we compute these lists of lists that get transformed and fed to @f@ as arguments:
        -- [ []
        -- , [x]   , [\x -> x]   , [\y -> x]   , [\x x -> x]   , ...
        -- , [y]   , [\x -> y]   , [\y -> y]   , [\x x -> y]   , ...
        -- , [x, x], [\x -> x, x], [\y -> x, x], [\x x -> x, x], ... , [x, \x -> x] , ...
        -- , [x, y], [\x -> x, y], [\y -> x, y], [\x x -> x, y], ... , [x, \x -> y] , ...
        -- ...
        -- ]
        args <- varRows 3
        for args $ \arg -> flip (,) arg <$> varRows 1
    (binds2, bindsDiff) <- splits binds1
    (args2 , argsDiff ) <- splits args1
    let mkLams = mkIterTyLam . map (\v -> TyVarDecl () v $ Type ())
        -- > mkTy [x, y] [([x1, y1], a), ([x2, y2], b)] ~>
        -- >   \x y -> f (\x1 y1 -> a) (\x2 y2 -> b)
        mkTy binds
            = mkLams binds
            . mkIterTyApp () (TyVar () f)
            . map (\(locs, body) -> mkLams locs $ TyVar () body)
        ty1 = mkTy binds1 args1
        ty2 = mkTy binds2 args2
        -- Answers this question: is 'ty2' a correct eta-contracted version of 'ty1'?
        -- Note that the eta-contractibility relation is reflexive.
        res = and
            [ -- Removed arguments of @f@ are the same variables, in exactly the same order,
              -- as removed outer lambda bindings.
              map ((,) []) bindsDiff == argsDiff
              -- All removed lambda bindings are different variables. We can't just require
              -- @allDistinct binds1@, because @(\x x -> f x) == (\x -> f)@ does hold.
            , allDistinct bindsDiff
              -- None of the removed lambda bindings are referenced in the remaining arguments.
              -- The @concatMap@ ensures that if a variable bound by an outer lambda is shadowed
              -- by a local lambda binding, then the outer variable is not referenced.
            , null $ bindsDiff `intersect` concatMap (\(locs, body) -> [body] \\ locs) args2
            ]
    -- We generate tuples like that:
    --
    --     ( \x y -> f (\y -> y) x y
    --     , f (\y -> y)
    --     , True
    --     )
    --
    -- The 'True' says that the second type is a correct eta-contracted version of the first type.
    -- "A correct" is due to the fact that it's also correct to eta-contract the first type to
    -- @\x -> f (\y -> y) x@ and such a test case gets generated as well.
    [(ty1, ty2, res)]

testEtaEquality :: Assertion
testEtaEquality =
    for_ tyEtaPairs $ \(ty1, ty2, b) ->
        unless (b == (ty1 == ty2)) . assertFailure $ displayPlcDef (ty1, ty2, b)

test_equality :: TestTree
test_equality =
    testGroup "equality"
        [ testCase "alpha" $ testAlphaEquality @?= True
        , testCase "shadowed variable" $ testRebindShadowedVariable @?= True
        , testCase "captured variable" $ testRebindCapturedVariable @?= True
        , testCase "eta" testEtaEquality
        ]
